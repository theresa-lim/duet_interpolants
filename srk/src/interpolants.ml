open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.interpolants" end)

module M = Map.Make(struct type t = int [@@deriving ord] end)
module CS = CoordinateSystem
module Interpolator = 
struct 

(* given polyhedrons pA and pB, computes the half-space interpolent that 
   seperates them*)
let halfITP srk dim variables (pA: Polyhedron.t) (pB: Polyhedron.t) = 
    let i = List.map (fun ind -> mk_symbol srk ~name:("i"^(string_of_int ind)) `TyReal) 
          (List.init dim (fun v -> v)) in (* what is dim here?? need a diff set of i *)
    let k = (mk_symbol srk ~name:"k" `TyReal) in 

  let phi (p: Polyhedron.t) (isA: bool) =
    let matrix_form = 
      Polyhedron.enum_constraints p
      |> BatEnum.fold (fun acc (typ, vec) -> 
        match typ with 
        | `Nonneg -> vec :: acc
        | `Pos -> assert false
        | `Zero -> vec :: (Linear.QQVector.negate vec) :: acc
        ) [] 
      in 
    let lambdas = List.mapi (fun i _ -> mk_symbol srk ~name:("lambda"^(string_of_int i)) `TyReal) matrix_form in

    let (i_sums, k_sum) = List.fold_left2 (fun (i_sums, k_sum) vec lambda ->
      Linear.QQVector.fold (fun ind v (i_sums, k_sum) ->  
        let term = mk_mul srk [mk_real srk v; mk_const srk lambda] in 
        if ind == Linear.const_dim then (i_sums, term :: k_sum)
        else 
          if M.mem ind i_sums then (M.add ind (term :: M.find ind i_sums) i_sums, k_sum) 
          else (M.add ind [term] i_sums, k_sum)
      ) vec (i_sums, k_sum)
      ) (M.empty, []) matrix_form lambdas in 

    let nonneg = List.map (fun sym -> mk_leq srk (mk_zero srk) (mk_const srk sym)) lambdas in 
    let i_constraints = 
      if isA then M.fold (fun ind sum acc ->
        mk_eq srk (mk_const srk (List.nth i ind)) (mk_add srk sum) :: acc
      ) i_sums [] 
      else M.fold (fun ind sum acc ->
        mk_eq srk (mk_neg srk (mk_const srk (List.nth i ind))) (mk_add srk sum) :: acc
      ) i_sums [] 
    in  
    let k_constraint = 
      if isA then mk_leq srk (mk_add srk k_sum) (mk_const srk k)(* shouldn't this be the other way around?*)
      else mk_not srk (mk_leq srk (mk_neg srk (mk_const srk k)) (mk_add srk k_sum))
    in 

    mk_and srk (k_constraint :: i_constraints @ nonneg)
  in
  let formula = mk_and srk [(phi pA true); (phi pB false)] in
  let model = Smt.get_model srk formula in
  match model with
  | `Sat interp -> 
    let k_value = Interpretation.real interp k |> mk_real srk in 
    let ix = List.map2 (fun coeff var -> mk_mul srk [mk_real srk (Interpretation.real interp coeff); var]) i variables 
    |> mk_add srk in 
    Some (mk_leq srk ix k_value)
  | _ -> None

  let cand srk dim vars (sA: Polyhedron.t list) (sB: Polyhedron.t list) : 'a formula option= 
    let rec cand_B (a: Polyhedron.t) (sB: Polyhedron.t list) acc = 
      match sB with
      | hd :: tl -> begin 
        match halfITP srk dim vars a hd with
        | Some f -> 
        cand_B a tl (mk_and srk [f ; acc])
        | None -> None
      end
      | [] -> Some acc
    in
    let rec cand_A (sA: Polyhedron.t list) (sB: Polyhedron.t list) acc =
      match sA with
      | hd :: tl -> begin
        match cand_B hd sB (mk_true srk) with
        | Some f -> cand_A tl sB (mk_or srk [(f); acc])
        | None -> None
      end
      | [] -> Some acc
    in
    cand_A sA sB (mk_false srk)

  let sample context (model: 'a Interpretation.interpretation) (phi: Polyhedron.t list) cs = 
    List.map (fun poly -> 
      let formula = (Polyhedron.to_formula cs poly) in 
      if Interpretation.evaluate_formula model formula then formula else mk_not context formula
    ) phi
    |> mk_and context 

  let formula_of_polyList srk cs ls= 
    List.map (Polyhedron.to_formula cs) ls |> List.fold_left (fun acc f -> mk_or srk [f; acc]) (mk_false srk)

  let interpolant srk vars dim cs (a: Polyhedron.t list) (b: Polyhedron.t list)=
    let formA = formula_of_polyList srk cs a in
    let formB = formula_of_polyList srk cs b in
    let rec aux (sA: Polyhedron.t list) (sB: Polyhedron.t list) =
      match cand srk dim vars sA sB with
      | Some c -> (
        match (Smt.get_model srk (mk_and srk [formA; mk_not srk c])) with
        | `Sat i -> begin
          let newSA = Polyhedron.of_implicant ~admit:true cs [(sample srk i a cs)] :: sA in
          aux newSA sB
        end
        | `Unsat -> begin 
          match (Smt.get_model srk (mk_and srk [formB; c])) with
          | `Sat i ->
            let newSB = Polyhedron.of_implicant ~admit:true cs [(sample srk i a cs)] :: sB in
            aux sA newSB
          | `Unsat -> Some c
          | `Unknown -> assert false
        end
        | `Unknown -> assert false
      )
      | None -> None
    in
    aux [] []

    let to_list ?exists:(p=fun _ -> true) cs srk (phi: 'a formula) : Polyhedron.t list=
      let solver = Smt.mk_solver srk in
      let phi_symbols = symbols phi in
      let symbol_list = Symbol.Set.elements phi_symbols in

    let disjuncts = ref 0 in
    let rec go list =
      Smt.Solver.push solver;
      Smt.Solver.add solver [mk_not srk (formula_of_polyList srk cs list)];
      let result =
        Log.time "lazy_dnf/sat" (Smt.Solver.get_concrete_model solver) symbol_list
      in
      match result with
      | `Unsat ->
        Smt.Solver.pop solver 1;
        list
      | `Unknown ->
        begin
          logf ~level:`warn "abstraction timed out (%d disjuncts); returning top"
            (!disjuncts);
          Smt.Solver.pop solver 1;
          [Polyhedron.top]
        end
      | `Sat interp -> begin
          Smt.Solver.pop solver 1;
          incr disjuncts;
          logf "[%d] abstract lazy_dnf" (!disjuncts);
          begin
            let disjunct =
              match Interpretation.select_implicant interp phi with
              | Some d -> Polyhedron.of_implicant ~admit:true cs d
              | None -> assert false
            in

            let valuation =
              let table : QQ.t array =
                Array.init (CS.dim cs) (fun i ->
                    Interpretation.evaluate_term
                      interp
                      (CS.term_of_coordinate cs i))
              in
              fun i -> table.(i)
            in
            let projected_coordinates =
              BatEnum.filter (fun i ->
                  match CS.destruct_coordinate cs i with
                  | `App (sym, _) -> not (p sym)
                  | _ -> true)
                (0 -- (CS.dim cs - 1))
              |> BatList.of_enum
            in
            let projected_disjunct =
              Polyhedron.local_project valuation projected_coordinates disjunct
            in
            go (projected_disjunct :: list)
          end
        end
    in
    Smt.Solver.add solver [phi];
    (Log.time "Abstraction" go [])

    let to_lists exists srk phi1 phi2= 
      let cs = CoordinateSystem.mk_empty srk in
      ((to_list ~exists cs srk phi1, to_list cs srk phi2), cs)
      
end