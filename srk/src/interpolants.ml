open Syntax

module M = Map.Make(struct type t = int [@@deriving ord] end)

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
      else mk_not srk (mk_leq srk (mk_add srk k_sum) (mk_neg srk (mk_const srk k)))
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

  let cand srk dim vars (sA: Polyhedron.t) (sB: Polyhedron.t) : 'a formula option= 
    let rec cand_B a sB acc = 
      (* need to get the variables from ??? A or B *)
      match BatEnum.get sB with
      | Some c -> begin 
        match halfITP srk dim vars (Polyhedron.of_constraints (BatEnum.singleton a)) (Polyhedron.of_constraints (BatEnum.singleton c)) with
        | Some f -> 
        cand_B a sB (mk_and srk [f ; acc])
        | None -> None
      end
      | None -> Some acc
    in
    let rec cand_A sA sB acc =
      match BatEnum.get sA with
      | Some c -> begin
        match cand_B c sB (mk_true srk) with
        | Some f -> cand_A sA sB (mk_or srk [(f); acc])
        | None -> None
      end
      | None -> Some acc
    in
    cand_A (Polyhedron.enum_constraints sA) (Polyhedron.enum_constraints sB) (mk_false srk)

  let sample context vars (model: 'a Interpretation.interpretation) (phi: Polyhedron.t) = 
    Polyhedron.enum_constraints phi 
    |> BatEnum.map (fun (typ, v) ->
      let formula = (match typ with 
      | `Nonneg -> mk_leq context (mk_zero context) (Linear.term_of_vec context (fun i -> List.nth vars i) v)
      | `Pos -> mk_lt context (mk_zero context) (Linear.term_of_vec context (fun i -> List.nth vars i) v)
      | `Zero -> mk_eq context (mk_zero context) (Linear.term_of_vec context (fun i -> List.nth vars i) v))
      in 
      if (Interpretation.evaluate_formula model formula) then formula else mk_not context formula
      )
    |> BatEnum.fold (fun acc v -> v :: acc) []
    |> mk_and context


  let interpolant srk vars dim cs (a: Polyhedron.t) (b: Polyhedron.t)=
    let formA = Polyhedron.to_formula cs a in
    let formB = Polyhedron.to_formula cs b in
    let rec aux sA sB =
      match cand srk dim vars sA sB with
      | Some c -> (
        match (Smt.get_model srk (mk_and srk [formA; mk_not srk c])) with
        | `Sat i -> begin
          let newSA = (Polyhedron.meet (Polyhedron.of_formula cs (sample srk vars i a)) sA) in
          aux newSA sB
        end
        | _ -> begin 
          match (Smt.get_model srk (mk_and srk [formB; c])) with
          | `Sat i ->
            let newSB = (Polyhedron.meet (Polyhedron.of_formula cs (sample srk vars i b)) sB) in
            aux sA newSB
          | _ -> c
        end
      )
      | None -> raise Exit
    in
    aux Polyhedron.bottom Polyhedron.bottom

(* to do: 
   figure out merging + splitting
   *)

end