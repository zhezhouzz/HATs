external method_predicates : t = "<"


let nonderter_dec =
  let a = (v > 0 : [%v: int]) [@over] in
  (0 <= v && v < a : [%v: int]) [@under]
