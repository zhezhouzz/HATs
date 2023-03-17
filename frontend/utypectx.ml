open Ast
open MultiUnderTypectx
open Zzdatatype.Datatype
open Sugar

let pretty_layout f ctx =
  List.split_by ";\n"
    (fun (name, ty) ->
      Printf.sprintf "%s:%s" name
        (List.split_by "∧" (fun x -> f x |> Pp.mk_red) ty))
    ctx

let pretty_print f ctx =
  Env.show_debug_typing @@ fun _ ->
  List.iter
    (fun (name, ty) ->
      Pp.printf "%s:@{<green>%s@}," name (List.split_by "∧" f ty))
    ctx

let pretty_layout_over = pretty_layout Overty.pretty_layout
let pretty_layout_judge ctx (e, ty) = Printf.sprintf "%s⊢\n%s :\n%s\n" ctx e ty

let pretty_layout_over_judge ctx (e, r) =
  pretty_layout_judge (pretty_layout_over ctx) (e, Overty.pretty_layout r)

(* let pretty_layout_under_judge ctx (e, (r : Languages.Qunderty.t)) = *)
(*   pretty_layout_judge (pretty_layout_under ctx) (e, Qunderty.pretty_layout r) *)

let pretty_layout_subtyping ctx (r1, r2) =
  Printf.sprintf "%s⊢\n%s <:\n%s\n" ctx r1 r2

let pretty_layout_over_subtyping ctx (r1, r2) =
  pretty_layout_subtyping
    (pretty_layout Overty.pretty_layout ctx)
    (Overty.pretty_layout r1, Overty.pretty_layout r2)

let pretty_layout_under_subtyping ctx (r1, r2) =
  pretty_layout_subtyping
    (pretty_layout Underty.pretty_layout ctx)
    (Underty.pretty_layout r1, Underty.pretty_layout r2)

let pretty_layout_raw (x : ctx) = pretty_layout Underty.pretty_layout x
let pretty_layout (x : ctx) = pretty_layout_raw x

let pretty_print (x : ctx) =
  Env.show_debug_typing (fun _ ->
      pretty_print Underty.pretty_layout x;
      print_newline ())

let pretty_layout_judge ctx (e, (r : UT.t)) =
  pretty_layout_judge (pretty_layout ctx) (e, Underty.pretty_layout r)

let pretty_print_judge ctx (e, (r : UT.t)) =
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Type Check:@}\n" in
      pretty_print ctx;
      Pp.printf "⊢ @{<magenta>%s@} ⇦ " (short_str 100 e);
      Pp.printf "@{<cyan>%s@}\n\n" @@ Underty.pretty_layout r)

let pretty_print_app_judge ctx (args, (r : UT.t)) =
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Application Type Check:@}\n" in
      pretty_print ctx;
      Pp.printf "⊢ @{<magenta>%s → ? @} ⇦ "
        (List.split_by " → " (fun x -> x.UL.x) args);
      Pp.printf "@{<cyan>%s@}\n\n" @@ Underty.pretty_layout r)

let pretty_print_infer ctx (e, (r : UT.t)) =
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Type Infer:@}\n" in
      pretty_print ctx;
      Pp.printf "⊢ @{<magenta>%s@} ⇨ " (short_str 100 e);
      Pp.printf "@{<cyan>%s@}\n\n" @@ Underty.pretty_layout r)

let pretty_layout_subtyping ctx (r1, r2) =
  pretty_layout_subtyping (pretty_layout ctx)
    (Underty.pretty_layout r1, Underty.pretty_layout r2)

let pretty_print_subtyping ctx (r1, r2) =
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Subtyping Check:@}\n" in
      pretty_print ctx;
      Pp.printf "⊢ @{<magenta>%s@} <: @{<cyan>%s@}\n\n"
        (Underty.pretty_layout r1) (Underty.pretty_layout r2))

let pretty_print_q uqvs eqvs pre body =
  Env.show_debug_queries (fun _ ->
      let () = Pp.printf "@{<bold>Query:@}\n" in
      Quantified.print_qt_ uqvs eqvs;
      Pp.printf "\n@{<cyan>%s@} @{<bold>=>@}\n@{<magenta>%s@}\n"
        (Autov.coq_layout_prop pre)
        (Autov.coq_layout_prop body))
