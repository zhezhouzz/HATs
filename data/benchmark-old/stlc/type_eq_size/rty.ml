let type_eq_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  let tau_a = (ty_size v s : [%v: stlc_ty]) [@over] in
  let tau_b = (true : [%v: stlc_ty]) [@over] in
  (iff v (type_eq_spec tau_a tau_b) : [%v: bool]) [@under]
