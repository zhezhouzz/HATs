let type_eq (tau_a : stlc_ty) (tau_b : stlc_ty) : bool =
  type_eq_size (nat_gen ()) tau_a tau_b
