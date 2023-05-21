let combine_terms =
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  let a =
    (typing gamma v tau && (is_const v || is_abs v) : [%v: stlc_term]) [@over]
  in
  let b = (typing gamma v tau && not (no_app v) : [%v: stlc_term]) [@over] in
  (typing gamma v tau : [%v: stlc_term]) [@under]
