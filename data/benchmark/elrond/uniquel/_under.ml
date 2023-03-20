external method_predicates : t = "mem" "len" ">="

let list_gen =
  let s = (v >= 0 : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (len v s && fun (u : [%forall: int]) -> implies (mem v u) (u == x)
    : [%v: int ulist])
    [@under]
