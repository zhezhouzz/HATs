let combine_terms (gamma : stlc_tyctx) (tau : stlc_ty) (a : stlc_term)
    (b : stlc_term) : stlc_term =
  if bool_gen () then or_var_in_typectx gamma tau a
  else or_var_in_typectx gamma tau b
