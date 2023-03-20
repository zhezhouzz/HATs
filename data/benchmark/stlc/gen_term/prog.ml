let gen_term (num_app : int) (tau : stlc_ty) (gamma : stlc_tyctx) : stlc_term =
  gen_term_size (nat_gen ()) num_app tau gamma
