open Language
module PCtx = PTypectx
module R = PCtxType
module P = PCtxType.P
module ECtx = Eqctx
module POpCtx = POpTypectx

(* open TypedCoreEff *)
open Sugar

let layout_comp = Denormalize.layout_comp
let layout_value = Denormalize.layout_value

type typectx = { eqctx : ECtx.ctx; rctx : PCtx.ctx; opctx : POpCtx.ctx }

let typectx_new_to_right typectx (binding : string R.typed) =
  { typectx with rctx = PCtx.new_to_right typectx.rctx binding }

let typectx_newopt_to_right typectx binding =
  match binding with
  | None -> typectx
  | Some binding -> typectx_new_to_right typectx binding

let typectx_new_to_rights typectx (binding : string R.typed list) =
  List.fold_left
    (fun typectx x -> typectx_new_to_right typectx x)
    typectx binding

let print_typectx typectx =
  Env.show_debug_typing (fun () ->
      (* Pp.printf "@{<bold>E:@} %s\n" "omitted"; *)
      (* Pp.printf "@{<bold>Op:@} %s\n" "omitted"; *)
      Pp.printf "@{<bold>R:@} %s\n"
        (PCtx.layout_typed_l (fun x -> x) typectx.rctx))

let print_subtyping typectx (t1, t2) =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>Subtyping:@}\n";
      Pp.printf "@{<bold>R:@} %s\n"
        (PCtx.layout_typed_l (fun x -> x) typectx.rctx);
      Pp.printf "⊢ @{<hi_magenta>%s@}\n<:@{<cyan>%s@}\n" (R.layout_rty t1)
        (R.layout_rty t2))

let print_wellformedness typectx tau =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>WellFormedness:@}\n";
      Pp.printf "@{<bold>R:@} %s\n"
        (PCtx.layout_typed_l (fun x -> x) typectx.rctx);
      Pp.printf "⊢WF @{<hi_magenta>%s@}\n" (R.layout_rty tau))

let print_typing_rule file line funcname rule =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>%s::%s@}(%s:%i)\n" funcname rule file line)

let subtyping_rty_bool file line typectx curA (t1, t2) =
  let t1 = Auxtyping.concat curA t1 in
  let t2 = Auxtyping.concat curA t2 in
  let () = Env.show_debug_typing (fun () -> print_subtyping typectx (t1, t2)) in
  if Subtyping.sub_rty_bool typectx.rctx typectx.eqctx t1 t2 then true
  else (
    Env.show_debug_typing (fun () ->
        Pp.printf "@{<orange> subtyping failed at [%s::%i]@}\n" file line);
    false)

let subtyping_pty_bool file line typectx (t1, t2) =
  let () =
    Env.show_debug_typing (fun () -> print_subtyping typectx (Pty t1, Pty t2))
  in
  if Subtyping.sub_pty_bool typectx.rctx typectx.eqctx t1 t2 then true
  else (
    Env.show_debug_typing (fun () ->
        Pp.printf "@{<orange> subtyping failed at [%s::%i]@}\n" file line);
    false)

let wellformedness_rty_bool typectx tau =
  let () = Env.show_debug_typing (fun () -> print_wellformedness typectx tau) in
  if Subtyping.is_bot_rty typectx.rctx typectx.eqctx tau then (
    Env.show_debug_typing (fun () ->
        Pp.printf "@{<orange> wellformedness failed@}\n");
    false)
  else true

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

let _force_not_empty_list file line = function
  | [] -> _failatwith file line "die"
  | _ -> ()
