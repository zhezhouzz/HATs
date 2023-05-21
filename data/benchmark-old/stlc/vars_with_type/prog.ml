let vars_with_type (gamma : stlc_tyctx) (tau : stlc_ty) : stlc_term =
  let (n2 : int) = nat_gen () in
  vars_with_type_size n2 gamma 0 tau
