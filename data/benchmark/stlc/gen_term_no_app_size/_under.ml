external method_predicates : t = "size" "typing" "is_abs" "is_const" "no_app" "is_ty_post" "is_ty_pre" "ty_size" "size_app" "typing_var"

let[@library] gen_const =
  let a = (true : [%v: unit]) [@over] in
  (is_const v : [%v: stlc_term]) [@under]

let[@library] or_var_in_typectx =
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  let a = (typing gamma v tau : [%v: stlc_term]) [@over] in
  ((typing gamma v tau
   && implies (no_app a) (no_app v)
   && fun (u : [%forall: int]) -> implies (size_app a u) (size_app v u))
   || typing_var gamma v tau
    : [%v: stlc_term])
    [@under]

let gen_term_no_app_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  let tau = (size v s : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && no_app v : [%v: stlc_term]) [@under]
