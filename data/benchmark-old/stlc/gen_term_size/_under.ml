external method_predicates : t = "dec_pair" "size" "typing" "no_app" "is_const" "is_abs" "is_ty_post" "is_ty_pre" "typing_var"

let[@library] nonderter_dec =
  let a = (v > 0 : [%v: int]) [@over] in
  (0 <= v && v < a : [%v: int]) [@under]

let[@library] gen_type =
  let s = (true : [%v: unit]) [@over] in
  (true : [%v: stlc_ty]) [@under]

let[@library] gen_const =
  let a = (true : [%v: unit]) [@over] in
  (is_const v : [%v: stlc_term]) [@under]

let[@library] combine_terms =
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  let a =
    (typing gamma v tau && (is_const v || is_abs v) : [%v: stlc_term]) [@over]
  in
  let b = (typing gamma v tau && not (no_app v) : [%v: stlc_term]) [@over] in
  (typing gamma v tau : [%v: stlc_term]) [@under]

let[@library] gen_term_no_app =
  let tau = (true : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && no_app v : [%v: stlc_term]) [@under]

let gen_term_size =
  let dec = (v >= 0 : [%v: int]) [@over] in
  let num_app = (v >= 0 : [%v: int]) [@over] in
  let tau = (dec_pair v dec num_app : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && size v num_app : [%v: stlc_term]) [@under]
