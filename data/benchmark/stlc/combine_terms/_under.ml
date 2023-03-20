external method_predicates : t = "typing" "size_app" "typing_var" "no_app" "is_const" "is_abs"

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

let combine_terms =
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  let a =
    (typing gamma v tau && (is_const v || is_abs v) : [%v: stlc_term]) [@over]
  in
  let b = (typing gamma v tau && not (no_app v) : [%v: stlc_term]) [@over] in
  (typing gamma v tau : [%v: stlc_term]) [@under]
