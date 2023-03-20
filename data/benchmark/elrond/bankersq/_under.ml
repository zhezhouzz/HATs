external method_predicates : t = "len"

let[@library] stream_gen =
  let a = (true : [%v: int]) [@over] in
  (fun (u : [%forall: int]) -> implies (0 <= u && u <= a) (len v u)
    : [%v: int stream])
    [@under]

let bankersq_gen =
  let s = (v >= 0 : [%v: int]) [@over] in
  (len v s : [%v: int bankersq]) [@under]
