external method_predicates : t = "size"

let[@library] gen_type_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  (size v s : [%v: stlc_ty]) [@under]

let gen_type =
  let s = (true : [%v: unit]) [@over] in
  (true : [%v: stlc_ty]) [@under]
