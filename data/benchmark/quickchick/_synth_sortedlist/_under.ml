external method_predicates : t = "rng" "mem" "ord" "<="
(* let[@library] gt_eq_int_gen =
  let (x0 : [%over: int]) = (true : [%v: int]) in
  (v >= x0 : [%v: int])

let[@library] sizecheck =
  let (x0 : [%over: int]) = (true : [%v: int]) in
  (iff v (x0 == 0) : [%v: bool])

let[@library] subs =
    let (s : [%over: int]) = (true : [%v: int]) in
    (v == (s - 1) : [%v: int])
   *)
  

let goal =
  let size = (0 <= v : [%v: int]) [@over] in
  let x0 = (true : [%v: int]) [@over] in
  (rng v size && fun (u : [%forall: int]) (w : [%forall: int]) ->
   implies (mem v u) (x0 <= u) && implies (ord v u w) (u <= w)
    : [%v: int list])
    [@under]

  
  

