let gen_type_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  (size v s : [%v: stlc_ty]) [@under]
