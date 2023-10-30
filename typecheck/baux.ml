open Language
module RCtx = RTypectx

(* module ECtx = Eqctx *)
module ROpCtx = ROpTypectx
open Rty

(* open TypedCoreEff *)
open Sugar

let layout_comp = Denormalize.layout_comp
let layout_value = Denormalize.layout_value

type typectx = { rctx : RCtx.ctx; opctx : ROpCtx.ctx }

let typectx_new_to_right typectx (binding : string rtyped) =
  { typectx with rctx = RCtx.new_to_right typectx.rctx binding }

let typectx_newopt_to_right typectx binding =
  match binding with
  | None -> typectx
  | Some binding -> typectx_new_to_right typectx binding

let typectx_new_to_rights typectx (binding : string rtyped list) =
  List.fold_left
    (fun typectx x -> typectx_new_to_right typectx x)
    typectx binding

let print_typectx typectx =
  Env.show_debug_typing (fun () ->
      (* Pp.printf "@{<bold>E:@} %s\n" "omitted"; *)
      (* Pp.printf "@{<bold>Op:@} %s\n" "omitted"; *)
      Pp.printf "@{<bold>R:@} %s\n" (RCtx.layout_typed_l typectx.rctx))

let print_subtyping_str typectx (t1, t2) =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>Subtyping:@}\n";
      Pp.printf "@{<bold>R:@} %s\n" (RCtx.layout_typed_l typectx.rctx);
      Pp.printf "⊢ @{<hi_magenta>%s@}\n<:@{<cyan>%s@}\n" t1 t2)

let print_subtyping typectx (t1, t2) =
  print_subtyping_str typectx (layout_rty t1, layout_rty t2)

let print_wellformedness typectx tau =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>WellFormedness:@}\n";
      Pp.printf "@{<bold>R:@} %s\n" (RCtx.layout_typed_l typectx.rctx);
      Pp.printf "⊢WF @{<hi_magenta>%s@}\n" (layout_rty tau))

let print_typing_rule file line funcname rule =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>%s::%s@}(%s:%i)\n" funcname rule file line)

let stat_rty_time_record = ref []
let stat_am_time_record = ref []

let stat_init () =
  stat_rty_time_record := [];
  stat_am_time_record := []

let stat_get_cur () = (!stat_rty_time_record, !stat_am_time_record)

let subtyping_srl_bool file line typectx (t1, t2) =
  let () =
    Env.show_debug_typing (fun () ->
        print_subtyping_str typectx (layout_regex t1, layout_regex t2))
  in
  let runtime, res =
    Sugar.clock (fun () -> Subtyping.sub_srl_bool typectx.rctx (t1, t2))
  in
  let () = stat_am_time_record := !stat_am_time_record @ [ runtime ] in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Pp.printf "@{<bold>subtyping_srl_bool: @}%f\n" runtime
  in
  if res then true
  else (
    Env.show_debug_typing (fun () ->
        Pp.printf "@{<orange> subtyping failed at [%s::%i]@}\n" file line);
    false)

let subtyping_rty_is_bot_bool file line typectx t1 =
  let () =
    Env.show_debug_typing (fun () ->
        print_subtyping_str typectx (layout_rty t1, "bot"))
  in
  let runtime, res =
    Sugar.clock (fun () -> Subtyping.is_bot_rty typectx.rctx t1)
  in
  let () = stat_rty_time_record := !stat_rty_time_record @ [ runtime ] in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Pp.printf "@{<bold>subtyping_rty_is_bot_bool: @}%f\n" runtime
  in
  if res then (
    Env.show_debug_typing (fun () ->
        Pp.printf "@{<orange> [%s::%i] %s is bot@}\n" file line (layout_rty t1));
    true)
  else false

let subtyping_rty_bool file line typectx (t1, t2) =
  let () = Env.show_debug_typing (fun () -> print_subtyping typectx (t1, t2)) in
  let runtime, res =
    Sugar.clock (fun () -> Subtyping.sub_rty_bool typectx.rctx (t1, t2))
  in
  let () = stat_rty_time_record := !stat_rty_time_record @ [ runtime ] in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Pp.printf "@{<bold>subtyping_rty_bool: @}%f\n" runtime
  in
  if res then true
  else (
    Env.show_debug_typing (fun () ->
        Pp.printf "@{<orange> subtyping failed at [%s::%i]@}\n" file line);
    false)

let print_infer_info1 file line rulename typectx str =
  print_typing_rule file line "Infer" rulename;
  print_typectx typectx;
  Env.show_debug_typing (fun () ->
      Pp.printf "⊢ @{<hi_magenta>%s@} ⇨ %s\n\n"
        (short_str (Env.get_max_printing_size ()) @@ str)
        "?")

let print_infer_info2 file line rulename typectx str rty =
  print_typing_rule file line "InferEnd" rulename;
  print_typectx typectx;
  Env.show_debug_typing (fun () ->
      Pp.printf "⊢ @{<hi_magenta>%s@} ⇨"
        (short_str (Env.get_max_printing_size ()) @@ str);
      Pp.printf "@{<cyan>%s@}\n\n"
        (match rty with None -> "BOT" | Some rty -> rty))

let print_check_info file line rulename typectx str rty =
  print_typing_rule file line "Check" rulename;
  print_typectx typectx;
  Env.show_debug_typing (fun () ->
      Pp.printf "⊢ @{<hi_magenta>%s@} ⇦"
        (short_str (Env.get_max_printing_size ()) @@ str);
      Pp.printf "@{<cyan>%s@}\n\n" @@ rty)

(* let print_check_regex_info file line rulename typectx str hty = *)
(*   print_typing_rule file line "Check" rulename; *)
(*   print_typectx typectx; *)
(*   Env.show_debug_typing (fun () -> *)
(*       Pp.printf "@{<bold>⊢@}\n@{<hi_magenta>%s@}\n" *)
(*         (short_str (Env.get_max_printing_size ()) @@ str); *)
(*       Pp.printf "@{<cyan>⇦ %s@}\n" @@ hty) *)

let _force_not_emrty_list file line = function
  | [] -> _failatwith file line "die"
  | _ -> ()
