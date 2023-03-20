external method_predicates : t = "gamma_size" "typing_var" "is_var_in_range" "is_tyctx_hd" "is_tyctx_tl" "type_eq_spec" "is_id_eq"

let[@library] type_eq =
  let tau_a = (true : [%v: stlc_ty]) [@over] in
  let tau_b = (true : [%v: stlc_ty]) [@over] in
  (iff v (type_eq_spec tau_a tau_b) : [%v: bool]) [@under]

let vars_with_type_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  let gamma = (gamma_size v s : [%v: stlc_tyctx]) [@over] in
  let offset = (v >= 0 : [%v: int]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  (is_var_in_range v offset s && typing_var gamma v tau
    : [%v: stlc_term])
    [@under]
