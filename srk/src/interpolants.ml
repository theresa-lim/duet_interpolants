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

  let cand srk dim vars (sA: Polyhedron.t list) (sB: Polyhedron.t list) : 'a formula option= 
    let rec cand_B (a: Polyhedron.t) (sB: Polyhedron.t list) acc = 
      (* need to get the variables from ??? A or B *)
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


(*
  sample (samples: polyhedron list) : polyhedron list <- Nikhil
   m = model
   A = 
    
  interpolant (A: polyhedron list) (B: polyhedron list)=
    sA = sample A
    sB = sample B
    C = cand sA sB
    while not (A -> C and C -> \neg B):
      populate pitp
      if PTIP = empty then SAT
      else
        ...

*)

(* to do: populate PItp (an ocaml map?)
   decide how we want to represent SA and SB (lists? there might be a more efficient data structure that I don't know about)
   do termination conditions
   figure out merging + splitting
   *)

end