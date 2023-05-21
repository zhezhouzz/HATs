external method_predicates : t = "rng" "mem" "ord" "<="

let sorted_list_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (rng v s && fun (u : [%forall: int]) (w : [%forall: int]) ->
   implies (mem v u) (x <= u) && implies (ord v u w) (u <= w)
    : [%v: int list])
    [@under]
