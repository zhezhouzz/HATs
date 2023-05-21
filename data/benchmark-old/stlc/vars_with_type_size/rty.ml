let vars_with_type_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  let gamma = (gamma_size v s : [%v: stlc_tyctx]) [@over] in
  let offset = (v >= 0 : [%v: int]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  (is_var_in_range v offset s && typing_var gamma v tau
    : [%v: stlc_term])
    [@under]
