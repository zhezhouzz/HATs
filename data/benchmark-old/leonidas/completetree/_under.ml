external method_predicates : t = "len" "complete"

let complete_tree_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (len v s && complete v : [%v: int ctree]) [@under]
