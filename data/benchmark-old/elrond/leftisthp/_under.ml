external method_predicates : t = "len"

let leftisthp_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (len v s : [%v: int leftisthp]) [@under]
