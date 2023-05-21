let gen_term_no_app (tau : stlc_ty) (gamma : stlc_tyctx) : stlc_term =
  gen_term_no_app_size (nat_gen ()) tau gamma
