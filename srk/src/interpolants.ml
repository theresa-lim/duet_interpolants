open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.interpolants" end)

type inequality = Open | Closed 
type sample = int * Polyhedron.t 
type collection = sample list 
module M = Map.Make(struct type t = int [@@deriving ord] end)
module CS = CoordinateSystem
module Interpolator = 
struct 

let _print_collection c = 
  print_string "\n collection: ";
  List.iter (fun (id, _) -> print_int id; print_string " ; ") c


let list_eq (a: collection) (b: collection) = 
  let sort_sample s = (List.sort (fun (id1, _) (id2, _) -> id1 - id2) s) in 
  List.length a = List.length b && List.for_all2 (fun (a, _) (b, _) -> a = b) (sort_sample a) (sort_sample b)

(* Randomly shuffle a list *)
  let shuffle d = 
    let nd = List.map (fun c -> (Random.bits (), c)) d in
    let sond = List.sort compare nd in
    List.map snd sond

(* given polyhedrons pA and pB, computes the half-space interpolent that 
   seperates them*)
let halfITP srk dim variables (pA: collection) (pB: collection) = 
    let i = List.map (fun ind -> mk_symbol srk ~name:("i"^(string_of_int ind)) `TyReal) 
          (List.init dim (fun v -> v)) in 
    let k = (mk_symbol srk ~name:"k" `TyReal) in 
    let openv = (mk_symbol srk ~name:"open" `TyBool) in 

  let phi (p: Polyhedron.t) (isA: bool) =
    let matrix_form = 
      Polyhedron.enum_constraints p
      |> BatEnum.fold (fun acc (typ, vec) -> 
        match typ with 
        | `Nonneg -> (Closed, vec) :: acc
        | `Pos -> (Open, vec) :: acc
        | `Zero -> (Closed, vec) :: (Closed, Linear.QQVector.negate vec) :: acc
        ) [] 
      in 
    let lambdas = List.mapi (fun i (typ, _) -> typ, mk_symbol srk ~name:("lambda"^(string_of_int i)) `TyReal) matrix_form in

    let (i_sums, k_sum) = List.fold_left2 (fun (i_sums, k_sum) (_, vec) (_, lambda) ->
      Linear.QQVector.fold (fun ind v (i_sums, k_sum) ->  
        let term = mk_mul srk [mk_real srk v; mk_const srk lambda] in 
        if ind == Linear.const_dim then (i_sums, term :: k_sum)
        else 
          if M.mem ind i_sums then (M.add ind (term :: M.find ind i_sums) i_sums, k_sum) 
          else (M.add ind [term] i_sums, k_sum)
      ) vec (i_sums, k_sum)
      ) (M.empty, []) matrix_form lambdas in 

    let nonneg = List.map (fun (_, sym) -> mk_leq srk (mk_zero srk) (mk_const srk sym)) lambdas in 
    let i_constraints = 
      if isA then M.fold (fun ind sum acc ->
        mk_eq srk (mk_neg srk (mk_const srk (List.nth i ind))) (mk_add srk sum) :: acc
      ) i_sums [] 
      else M.fold (fun ind sum acc ->
        mk_eq srk ((mk_const srk (List.nth i ind))) (mk_add srk sum) :: acc
      ) i_sums [] 
    in  
    let k_constraint = 
      if isA then mk_leq srk (mk_add srk k_sum) (mk_const srk k)
      else (mk_leq srk (mk_add srk k_sum) (mk_neg srk (mk_const srk k)))
    in 
    let zero_open = List.filter_map (fun (typ, lambda) ->
        match typ with 
        | Open -> Some (mk_eq srk (mk_const srk lambda) (mk_zero srk)) 
        | Closed -> None
      ) lambdas |> mk_and srk in 
    let op_phi = if isA 
      then mk_if srk (mk_and srk [mk_eq srk (mk_add srk k_sum) (mk_const srk k); zero_open]) (mk_not srk (mk_const srk openv)) 
      else mk_if srk (mk_and srk [mk_eq srk (mk_add srk k_sum) (mk_neg srk (mk_const srk k)); zero_open]) ((mk_const srk openv)) in 

    mk_and srk (k_constraint :: op_phi :: i_constraints @ nonneg)
  in
  let formula = mk_and srk ((List.map (fun (_, p) -> phi p true) pA) @ List.map (fun (_, p) -> phi p false) pB) in 
  let model = Smt.get_model srk formula in
  match model with
  | `Sat interp -> 
    let k_value = Interpretation.real interp k |> mk_real srk in 
    let ix = List.map2 (fun coeff var -> mk_mul srk [mk_real srk (Interpretation.real interp coeff); var]) i variables 
    |> mk_add srk in 
    Some (if Interpretation.bool interp openv then (mk_lt srk ix k_value) else (mk_leq srk ix k_value))
  | _ -> None

  let cand srk dim vars (sA: collection list) (sB: collection list) : 'a formula option * ((collection * collection) option)= 
    let rec cand_B (a: collection) (sB: collection list) acc = 
      match sB with
      | hd :: tl -> begin 
        match halfITP srk dim vars a hd with
        | Some f -> 
        cand_B a tl (mk_and srk [f ; acc])
        | None -> None, Some (a, hd)
      end
      | [] -> Some acc, None
    in
    let rec cand_A (sA: collection list) (sB: collection list) acc =
      match sA with
      | hd :: tl -> begin
        match cand_B hd sB (mk_true srk) with
        | Some f, None -> cand_A tl sB (mk_or srk [(f); acc])
        | None, Some (a, b) -> None, Some (a, b)
        | _ -> assert false
      end
      | [] -> Some acc, None
    in
    cand_A sA sB (mk_false srk)

  let sample _srk (model: 'a Interpretation.interpretation) (phi: Polyhedron.t list) cs id_ref = 
    let atoms = List.fold_left (fun b p -> BatEnum.append b (Polyhedron.enum_constraints p)) (BatEnum.empty ()) phi in 
    let atoms = BatEnum.fold (fun acc (typ, v) -> match typ with 
        | `Zero -> BatEnum.append (BatEnum.append (BatEnum.singleton (`Nonneg, v)) (BatEnum.singleton (`Nonneg, (Linear.QQVector.negate v)))) (acc)
        | _ -> BatEnum.append (BatEnum.singleton (typ, v)) (acc)
      ) (BatEnum.empty ()) atoms in 
    let val_of_int = (fun i -> CoordinateSystem.term_of_coordinate cs i |> Interpretation.evaluate_term model)in 
    let constr = BatEnum.map (fun (kind, v) -> 
      match kind with 
      | `Nonneg -> if (QQ.leq QQ.zero (Linear.evaluate_affine val_of_int v)) 
        then (`Nonneg, v) else (`Pos, Linear.QQVector.negate v)
      | `Pos -> if (QQ.lt QQ.zero (Linear.evaluate_affine val_of_int v)) 
        then (`Pos, v) else (`Nonneg, Linear.QQVector.negate v)
      (* Line 118 replaces ax = b with ax <= b && ax >= b, so this should be inaccessible *)
      | `Zero -> assert false
    ) atoms in 
    id_ref := !id_ref + 1;
    !id_ref, Polyhedron.of_constraints constr

  let merge (s: collection) (ls : collection list) (marked : collection list) = 
    let ls = shuffle ls in 
    let rec try_merging s ls = match ls with 
    | [] -> [s]
    | hd :: tl -> 
        if List.mem (s @ hd) marked 
          then hd :: (try_merging s tl)
          else (s @ hd) :: tl
    in 
    try_merging s ls

  (* Split collection c, remove c from ls, and insert the resulting splitted collections back into ls *)
  let split (c : collection) (ls : collection list) (marked : collection list) = 
    let c = shuffle c in 
    let pivot = Random.int ((List.length c) - 1) in
    let ls = List.filter (fun col -> not (list_eq col c)) ls in 
    let f, s = List.filteri (fun i _ -> i <= pivot) c, List.filteri (fun i _ -> i > pivot) c in 
    let marked = (f @ s) :: marked in 
    merge f (merge s ls marked) marked


  let formula_of_polyList srk cs ls= 
    List.map (Polyhedron.to_formula cs) ls |> List.fold_left (fun acc f -> mk_or srk [f; acc]) (mk_false srk)

  let interpolant srk vars dim cs (a: Polyhedron.t list) (b: Polyhedron.t list )=
    let sample_id_ref = ref 0 in 
    let formA = formula_of_polyList srk cs a in
    let formB = formula_of_polyList srk cs b in
    print_string "\n A formula: "; print_string (SrkUtil.mk_show (Syntax.pp_expr_unnumbered srk) formA) ;
    print_string "\n B formula: "; print_string (SrkUtil.mk_show (Syntax.pp_expr_unnumbered srk) formA) ; print_string "\n\n";
    let rec aux (sA: collection list) (sB: collection list) (marked: collection list) = 
        match cand srk dim vars sA sB with
      | Some c, None -> (
        match (Smt.get_model srk (mk_and srk [formA; mk_not srk c])) with
        | `Sat i -> begin
          let newSA = merge [(sample srk i a cs sample_id_ref)] sA marked in
          aux newSA sB marked 
        end
        | `Unsat -> begin 
          match (Smt.get_model srk (mk_and srk [formB; c])) with
          | `Sat i ->
            let newSB = merge [(sample srk i b cs sample_id_ref)] sB marked in
            aux sA newSB marked 
          | `Unsat -> Some c
          | `Unknown -> assert false
        end
        | `Unknown -> assert false
      )
      | None, Some (a, b) -> begin 
        match (a, b) with 
        | _ :: _ :: _, _ -> let sA = split a sA marked in aux sA sB (a :: marked)
        | _, _ :: _ :: _ -> let sB = split b sB marked in aux sA sB (b :: marked) 
        | _ -> 
          print_string (SrkUtil.mk_show (Syntax.pp_expr_unnumbered srk) (Polyhedron.to_formula cs (snd (List.hd a)))) ;
          None
        end
      | _ -> assert false
    in
    aux [] [] []

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
      (* Very hacky here: we assume that the coordinate systems "line up". 
         Eventually, this should be resolved by taking a single file as input and splitting up
         A and B in some way.   
         In the meantime, it's a good idea to inspect the formulas visually to ensure that the 
         variables look right.
      *)
      let throwaway = CoordinateSystem.mk_empty srk in
      ((to_list ~exists cs srk phi1, to_list throwaway srk phi2), cs)
      
end