open Ast.Ntyped
open Ast.Q

let mk_q_ (q, x, e) =
  let q = match q with Fa -> "∀ " | Ex -> "∃ " in
  Printf.sprintf "%s%s, %s" q x e

let mk_q (q, x, e) = mk_q_ (q, x.x, e)
let mk_uqs_ xs = List.fold_right (fun x e -> mk_q_ (Fa, x, e)) xs ""
let mk_eqs_ xs = List.fold_right (fun x e -> mk_q_ (Ex, x, e)) xs ""
let mk_uqs xs = List.fold_right (fun x e -> mk_q (Fa, x, e)) xs ""
let mk_eqs xs = List.fold_right (fun x e -> mk_q (Ex, x, e)) xs ""
let layout_qt_ uqvs eqvs qbody = mk_uqs_ uqvs ^ mk_eqs_ eqvs ^ qbody
let layout_qt uqvs eqvs qbody = mk_uqs uqvs ^ mk_eqs eqvs ^ qbody

let print_qt uqvs eqvs =
  Env.show_debug_typing @@ fun _ ->
  Pp.printf "@{<yellow>%s@}@{<green>%s@}" (mk_uqs uqvs) (mk_eqs eqvs)

let print_qt_ uqvs eqvs =
  Env.show_debug_typing @@ fun _ ->
  Pp.printf "@{<yellow>%s@}@{<green>%s@}" (mk_uqs_ uqvs) (mk_eqs_ eqvs)
