let rec gen_type_size (size : int) : stlc_ty =
  if size == 0 then Stlc_ty_nat
  else
    let (size0 : int) = size - 1 in
    let (size1 : int) = int_range_inc 0 size0 in
    let (size2 : int) = size0 - size1 in
    let (tau1 : stlc_ty) = gen_type_size size1 in
    let (tau2 : stlc_ty) = gen_type_size size2 in
    Stlc_ty_arr (tau1, tau2)
