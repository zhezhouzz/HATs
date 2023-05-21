external method_predicates : t = "size" "typing" "no_app"

let[@library] gen_term_no_app_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  let tau = (size v s : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && no_app v : [%v: stlc_term]) [@under]

let gen_term_no_app =
  let tau = (true : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && no_app v : [%v: stlc_term]) [@under]
