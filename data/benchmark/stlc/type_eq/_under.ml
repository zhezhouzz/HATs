external method_predicates : t = "ty_size" "type_eq_spec"

let[@library] type_eq_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  let tau_a = (ty_size v s : [%v: stlc_ty]) [@over] in
  let tau_b = (true : [%v: stlc_ty]) [@over] in
  (iff v (type_eq_spec tau_a tau_b) : [%v: bool]) [@under]

let type_eq =
  let tau_a = (true : [%v: stlc_ty]) [@over] in
  let tau_b = (true : [%v: stlc_ty]) [@over] in
  (iff v (type_eq_spec tau_a tau_b) : [%v: bool]) [@under]
