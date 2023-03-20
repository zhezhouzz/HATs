let[@library] stlc_ty_nat = (num_arr v 0 : [%v: stlc_ty]) [@under]

let[@library] stlc_ty_arr =
  let a =
    (fun (u : [%forall: int]) -> implies (num_arr v u) (u > 0)
      : [%v: stlc_ty])
      [@over]
  in
  ( (is_ty_pre a v : [%v: stlc_ty]) [@under],
    (is_ty_post a v : [%v: stlc_ty]) [@under] )
