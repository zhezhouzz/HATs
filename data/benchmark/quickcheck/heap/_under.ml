external method_predicates : t = "len" "heap" "hd" "<="

let heap_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  let max = (true : [%v: int]) [@over] in
  (heap v && len v s && fun (u : [%forall: int]) -> implies (hd v u) (u <= max)
    : [%v: int heap])
    [@under]
