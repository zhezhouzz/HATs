open Zzdatatype.Datatype
open Ast
open Sugar
open MMT

let ut_with_eq_pretty_layout = function
  | UtNormal t -> Underty.pretty_layout t
  | UtCopy id -> spf "[v = %s]" id.x

let mmt_pretty_layout t =
  match t with
  | Ot t -> Underty.ot_pretty_layout t
  | Consumed t -> spf "⟬ %s ⟭" (ut_with_eq_pretty_layout t)
  | Ut t -> ut_with_eq_pretty_layout t

let pretty_layout f ctx =
  List.split_by ";\n"
    (fun (name, ty) ->
      Printf.sprintf "%s:%s" name (f ty)
      (* (List.split_by "∧" (fun x -> f x |> Pp.mk_red) ty) *))
    ctx

let pretty_print f ctx =
  Env.show_debug_typing (fun _ ->
      if List.length ctx == 0 then Pp.printf "@{<green>∅@}"
      else
        List.iter
          (fun (name, ty) ->
            Pp.printf "%s:@{<green>%s@}," name (f ty)
            (* (List.split_by "∧" f ty) *))
          ctx)

let pretty_print_lines f ctx =
  Env.show_debug_typing (fun _ ->
      if List.length ctx == 0 then Pp.printf "@{<green>∅@}"
      else
        List.iter
          (fun (name, ty) ->
            Pp.printf "%s:@{<green>%s@}\n" name (f ty)
          ctx)

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
    (pretty_layout mmt_pretty_layout ctx)
    (mmt_pretty_layout r1, mmt_pretty_layout r2)

let pretty_print x =
  Env.show_debug_typing (fun _ ->
      pretty_print mmt_pretty_layout x;
      print_newline ())

let pretty_print_infer ctx (e, (r : UT.t)) =
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Type Infer:@}\n" in
      pretty_print ctx;
      Pp.printf "⊢ @{<hi_magenta>%s@} ⇨ " (short_str 100 e);
      Pp.printf "@{<cyan>%s@}\n\n" @@ Underty.pretty_layout r)

let pretty_print_judge ctx (e, (r : UT.t)) =
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Type Check:@}\n" in
      pretty_print ctx;
      Pp.printf "⊢ @{<hi_magenta>%s@} ⇦ " (short_str 10000 e);
      Pp.printf "@{<cyan>%s@}\n\n" @@ Underty.pretty_layout r)

let pretty_print_app_judge fname ctx (args, r) =
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Application Type Check (%s):@}\n" fname in
      pretty_print ctx;
      Pp.printf "⊢ @{<hi_magenta>%s → ? @} ⇦ "
        (List.split_by " → "
           (fun (x, ty) -> spf "%s:%s" x (ut_with_eq_pretty_layout ty))
           args);
      Pp.printf "@{<cyan>%s@}\n\n" @@ mmt_pretty_layout r)

let pretty_print_subtyping ctx (r1, r2) =
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Subtyping Check:@}\n" in
      pretty_print ctx;
      Pp.printf "⊢ @{<hi_magenta>%s@} <: @{<cyan>%s@}\n\n"
        (mmt_pretty_layout r1) (mmt_pretty_layout r2))

let pretty_print_q uqvs eqvs pre body =
  Env.show_debug_queries (fun _ ->
      let () = Pp.printf "@{<bold>Query:@}\n" in
      Quantified.print_qt_ uqvs eqvs;
      Pp.printf "\n@{<cyan>%s@} @{<bold>=>@}\n@{<hi_magenta>%s@}\n"
        (Autov.pretty_layout_prop pre)
        (Autov.pretty_layout_prop body))
(* (Autov.coq_layout_prop pre) *)
(* (Autov.coq_layout_prop body) *)
