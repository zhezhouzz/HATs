let rec gen_term_size (dec : int) (num_app : int) (tau : stlc_ty)
    (gamma : stlc_tyctx) : stlc_term =
  if num_app == 0 then gen_term_no_app tau gamma
  else
    let (num_app_func : int) = int_range_inex 0 num_app in
    let (num_app_arg : int) = int_range_inex 0 (num_app - num_app_func) in
    let (arg_tau : stlc_ty) = gen_type () in
    let (dec_dec : int) = nonderter_dec dec in
    let (func : stlc_term) =
      gen_term_size dec_dec num_app_func (Stlc_ty_arr (arg_tau, tau)) gamma
    in
    let (arg : stlc_term) = gen_term_size dec_dec num_app_arg arg_tau gamma in
    let (app_term : stlc_term) = Stlc_app (func, arg) in
    let (close_term : stlc_term) =
      match tau with
      | Stlc_ty_nat -> gen_const ()
      | Stlc_ty_arr (tau1, tau2) ->
          let (body : stlc_term) =
            gen_term_size dec_dec num_app tau2 (Stlc_tyctx_cons (tau1, gamma))
          in
          Stlc_abs (tau1, body)
    in
    combine_terms gamma tau close_term app_term
