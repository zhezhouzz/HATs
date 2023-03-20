let vars_with_type =
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  (typing_var gamma v tau : [%v: stlc_term]) [@under]
