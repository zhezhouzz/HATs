open Language
module Nt = Normalty.Ntyped
module R = Rty
open R
open Sugar

type fe = F | E

let decide_fa = function
  | Under, Under -> E
  | Over, Under -> F
  | Over, Over -> E
  | Under, Over -> F

let fa_base x (xou, { v = xv; phi = xphi }) (ou, { v; phi }) =
  let open P in
  let fa = decide_fa (xou, ou) in
  let concat (a, b) =
    match fa with F -> smart_implies (a, b) | E -> smart_and [ a; b ]
  in
  let q (x, body) =
    match fa with F -> Forall (x, body) | E -> Exists (x, body)
  in
  match x.ty with
  | Nt.Ty_unit -> R.{ v; phi = concat (xphi, phi) }
  | _ ->
      let xphi = P.subst (xv.x, AVar x) xphi in
      (* TODO: optimization, exists x, x = y /\ ... *)
      R.{ v; phi = q (x, concat (xphi, phi)) }

let rec flip_xty xty =
  match xty with
  | BaseRty { ou; basety } -> BaseRty { ou = ou_flip ou; basety }
  | Traced { h; pre; rty; post } -> Traced { h; pre; rty = flip_xty rty; post }
  | _ -> _failatwith __FILE__ __LINE__ "?"

let rec fa_function_ x xty rty =
  match rty with
  | BaseRty { ou; basety } -> (
      match xty with
      | BaseRty { ou = xou; basety = xbasety } ->
          let basety = fa_base x (xou, xbasety) (ou, basety) in
          BaseRty { ou; basety }
      | Traced { h; pre; rty = xty; post } ->
          Traced { h; pre; rty = fa_function_ x xty rty; post }
      | _ -> _failatwith __FILE__ __LINE__ "?")
  | Traced { h; pre; rty; post } -> (
      match xty with
      | BaseRty _ -> Traced { h; pre; rty = fa_function_ x xty rty; post }
      | Traced { h = h_prev; pre = pre_prev; rty = xty; post = post_prev } ->
          let h1_old = Nt.(h #: (erase_basety pre)) in
          let h1 = Nt.((Rename.unique h) #: (erase_basety pre)) in
          let post_prev_phi = subst_basety_by_id h1 post_prev in
          let pre_phi = subst_basety_by_id h1 pre in
          let rty = subst_id (h1_old, h1) rty in
          let post = subst_basety_id (h1_old, h1) post in
          let post =
            match
              fa_function_ x xty (BaseRty { ou = Under; basety = post })
            with
            | BaseRty { basety; _ } -> basety
            | _ -> _failatwith __FILE__ __LINE__ "?"
          in
          let h2 = Nt.((Rename.unique h) #: (erase_basety pre)) in
          let post_phi = subst_basety_by_id h2 post in
          let concat_phi = P.(Lit (mk_concat h1 h2 post.v)) in
          let phi' =
            P.smart_and [ post_prev_phi; pre_phi; post_phi; concat_phi ]
          in
          let post = { post with phi = P.(Exists (h1, Exists (h2, phi'))) } in
          Traced
            { h = h_prev; pre = pre_prev; rty = fa_function_ x xty rty; post }
      | _ -> _failatwith __FILE__ __LINE__ "?")
  | DepRty { dep; label; rarg; retrty } ->
      let rarg = rarg.x #: (fa_function_ x (flip_xty xty) rarg.ty) in
      DepRty { dep; label; rarg; retrty = fa_function_ x xty retrty }

let exists_function x rty =
  let x_typed = P.( #: ) x.x (erase x.ty) in
  let res = fa_function_ x_typed x.ty rty in
  let () =
    Env.show_debug_typing (fun _ ->
        Pp.printf
          "@{<bold>Exists@} @{<yellow>%s:%s@}@{<bold> ===> @}@{<orange>%s@}:\n\
           \t\t@{<green>%s@}\n"
          x.x (layout x.ty) (layout rty) (layout res))
  in
  res

let exists_base_function x xbasety basety =
  let x_typed = P.( #: ) x (erase_basety xbasety) in
  let res = fa_base x_typed (Under, xbasety) (Under, basety) in
  let () =
    Env.show_debug_typing (fun _ ->
        Pp.printf
          "@{<bold>ExistsBase@} @{<yellow>%s:%s@}@{<bold> ===> @}@{<orange>%s@}:\n\
           \t\t@{<green>%s@}\n"
          x (layout_basety xbasety) (layout_basety basety) (layout_basety res))
  in
  res
