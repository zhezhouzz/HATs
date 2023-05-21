let gen_type =
  let s = (true : [%v: unit]) [@over] in
  (true : [%v: stlc_ty]) [@under]
