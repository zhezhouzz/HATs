let or_var_in_typectx (gamma : stlc_tyctx) (tau : stlc_ty) (a : stlc_term) :
    stlc_term =
  if bool_gen () then a else vars_with_type gamma tau
