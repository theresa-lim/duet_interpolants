open Syntax

module M = Map.Make(struct type t = int [@@deriving ord] end)

module Interpolator = 
struct 

let phiA (p : Polyhedron.t) srk =
  let dim = Polyhedron.max_constrained_dim p in 
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
  
  let i = List.map (fun ind -> mk_symbol srk ~name:("i"^(string_of_int ind)) `TyReal) 
        (List.init dim (fun v -> v)) in 
  let k = mk_symbol srk ~name:"k" `TyReal in 

  let nonneg = List.map (fun sym -> mk_leq srk (mk_zero srk) (mk_const srk sym)) lambdas in 
  let i_constraints = M.fold (fun ind sum acc ->
      mk_eq srk (mk_const srk (List.nth i ind)) (mk_add srk sum) :: acc
    ) i_sums [] in  
  let k_constraint = mk_leq srk (mk_const srk k) (mk_add srk k_sum) in 

  mk_and srk (k_constraint :: i_constraints @ nonneg)




end