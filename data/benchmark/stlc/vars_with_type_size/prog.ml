let rec vars_with_type_size (size_gamma : int) (gamma : stlc_tyctx)
    (offset : int) (tau : stlc_ty) : stlc_term =
  match gamma with
  | Stlc_tyctx_nil -> Exn
  | Stlc_tyctx_cons (tau_hd, gamma_rest) ->
      let (id : stlc_term) =
        vars_with_type_size (size_gamma - 1) gamma_rest (offset + 1) tau
      in
      if bool_gen () then id
      else if type_eq tau_hd tau then
        let (t2 : stlc_term) = Stlc_id offset in
        t2
      else Exn
