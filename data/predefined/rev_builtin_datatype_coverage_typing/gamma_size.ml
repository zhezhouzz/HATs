let[@library] nil = (len v 0 : [%v: int list]) [@under]
let[@library] stlc_ty_nat = (ty_size v 0 : [%v: stlc_ty]) [@under]

let[@library] stlc_ty_arr =
  let a =
    (fun (u : [%forall: int]) -> implies (ty_size v u) (u > 0)
      : [%v: stlc_ty])
      [@over]
  in
  ( (is_ty_pre a v : [%v: stlc_ty]) [@under],
    (is_ty_post a v : [%v: stlc_ty]) [@under] )

let[@library] stlc_tyctx_nil = (gamma_size v 0 : [%v: stlc_tyctx]) [@under]

let[@library] stlc_tyctx_cons =
  let a =
    (fun (u : [%forall: int]) -> implies (gamma_size v u) (u > 0)
      : [%v: stlc_tyctx])
      [@over]
  in
  ( (is_tyctx_hd a v : [%v: stlc_ty]) [@under],
    (is_tyctx_tl a v : [%v: stlc_tyctx]) [@under] )
