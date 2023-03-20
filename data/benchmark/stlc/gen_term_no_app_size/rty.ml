let gen_term_no_app_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  let tau = (size v s : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && no_app v : [%v: stlc_term]) [@under]
