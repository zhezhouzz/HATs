let rec type_eq_size (s : int) (tau_a : stlc_ty) (tau_b : stlc_ty) : bool =
  match tau_a with
  | Stlc_ty_nat -> (
      match tau_b with
      | Stlc_ty_nat -> true
      | Stlc_ty_arr (tau_b_1, tau_b_2) -> false)
  | Stlc_ty_arr (tau_a_1, tau_a_2) -> (
      match tau_b with
      | Stlc_ty_nat -> false
      | Stlc_ty_arr (tau_b_1, tau_b_2) ->
          let (s_dec : int) = s - 1 in
          if type_eq_size s_dec tau_a_1 tau_b_1 then
            type_eq_size s_dec tau_a_2 tau_b_2
          else false)
