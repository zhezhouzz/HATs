let rec gen_term_no_app_size (size_of_tau : int) (tau : stlc_ty)
    (gamma : stlc_tyctx) : stlc_term =
  let (close_term : stlc_term) =
    match tau with
    | Stlc_ty_nat -> gen_const ()
    | Stlc_ty_arr (tau1, tau2) ->
        let (body : stlc_term) =
          gen_term_no_app_size (int_gen ()) tau2 (Stlc_tyctx_cons (tau1, gamma))
        in
        Stlc_abs (tau1, body)
  in
  or_var_in_typectx gamma tau close_term
