open Language
module RCtx = RTypectx
module R = Rty
module P = Rty.P
module ECtx = Eqctx
open TypedCoreEff
open Sugar

let layout_comp = Denormalize.layout_comp
let layout_value = Denormalize.layout_value

type typectx = { eqctx : ECtx.ctx; rctx : RCtx.ctx }

let typectx_new_to_right { rctx; eqctx } binding =
  { rctx = RCtx.new_to_right rctx binding; eqctx }

let typectx_new_to_rights { rctx; eqctx } binding =
  { rctx = RCtx.new_to_rights rctx binding; eqctx }
(* exception TypeErr of string *)

let print_typrctx { eqctx; rctx } =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>E:@} %s\n" "omitted";
      Pp.printf "@{<bold>R:@} %s\n" (RCtx.layout_typed_l (fun x -> x) rctx))

let print_subtyping typectx (t1, t2) =
  let () =
    Env.show_debug_typing (fun () -> Pp.printf "@{<bold>Subtyping:@}\n")
  in
  print_typrctx typectx;
  Env.show_debug_typing (fun () ->
      Pp.printf "⊢ %s\n<:%s\n" (R.layout_rty t1) (R.layout_rty t2))

let print_typing_rule file line funcname rule =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>%s::%s@}(%s:%i)\n" funcname rule file line)

let subtyping_rty_bool { eqctx; rctx; _ } (t1, t2) =
  if Subtyping.sub_rty_bool rctx eqctx t1 t2 then true
  else (
    Env.show_debug_typing (fun () ->
        Pp.printf "@{<orange> subtyping failed@}\n");
    false)

let rec _value_to_lit file line v =
  match v.x with
  | VVar name -> P.AVar name
  | VConst c -> P.AC c
  | VLam _ -> _failatwith file line "?"
  | VFix _ -> _failatwith file line "?"
  | VTu _ -> _failatwith file line "?"

let unify_arr_ret v rty =
  let open R in
  match rty with
  | Pty (ArrPty { rarg; retrty }) -> (
      let lit = _value_to_lit __FILE__ __LINE__ v in
      match rarg.px with None -> retrty | Some x -> subst (x, lit) retrty)
  | _ -> _failatwith __FILE__ __LINE__ ""

(* let layout_mode = TypeInfer -> "TypeInfer" | TypeCheck -> "TypeCheck" *)
let print_infer_info1 file line rulename typectx str =
  print_typing_rule file line "Infer%s" rulename;
  print_typrctx typectx;
  Env.show_debug_typing (fun () ->
      Pp.printf "⊢ @{<hi_magenta>%s@} ⇨ %s" (short_str 100 @@ str) "?")

let print_infer_info2 file line rulename typectx str rty =
  print_typing_rule file line "InferEnd" rulename;
  print_typrctx typectx;
  Env.show_debug_typing (fun () ->
      Pp.printf "⊢ @{<hi_magenta>%s@} ⇨" (short_str 100 @@ str);
      Pp.printf "@{<cyan>%s@}\n\n" @@ R.layout rty)

let print_check_info file line rulename typectx str rty =
  print_typing_rule file line "Check" rulename;
  print_typrctx typectx;
  Env.show_debug_typing (fun () ->
      Pp.printf "⊢ @{<hi_magenta>%s@} ⇦" (short_str 100 @@ str);
      Pp.printf "@{<cyan>%s@}\n\n" @@ R.layout rty)

let rec value_type_infer { rctx; eqctx } (value : value typed) : R.t =
  let str = layout_value value in
  let before_info line rulename =
    print_infer_info1 __FILE__ line rulename { rctx; eqctx } str
  in
  let end_info line rulename rty =
    print_infer_info2 __FILE__ line rulename { rctx; eqctx } str rty
  in
  let rty =
    match value.x with
    | VConst c ->
        let () = before_info __LINE__ "Const" in
        let rty =
          match c with
          | Const.U -> R.unit_ty
          | _ -> R.Pty (R.mk_pty_var_eq_c value.Nt.ty c)
        in
        let () = end_info __LINE__ "Const" rty in
        rty
    | VVar x ->
        let () = before_info __LINE__ "Var" in
        let rty = RCtx.get_ty rctx x in
        let rty =
          if Nt.is_basic_tp value.ty then
            R.Pty (R.mk_pty_var_eq_var x #: value.ty)
          else rty
        in
        let () = end_info __LINE__ "Var" rty in
        rty
    | _ -> _failatwith __FILE__ __LINE__ ""
  in
  rty

and comp_type_infer typectx (comp : comp typed) : R.t =
  let str = layout_comp comp in
  let before_info line rulename =
    print_infer_info1 __FILE__ line rulename typectx str
  in
  let end_info line rulename rty =
    print_infer_info2 __FILE__ line rulename typectx str rty
  in
  let rty =
    match comp.x with
    | CVal v -> value_type_infer typectx v #: comp.ty
    | CApp { appf; apparg } ->
        let () = before_info __LINE__ "App" in
        let f_rty = value_type_infer typectx appf in
        let f_rty_argty = R.get_argty f_rty in
        let () = value_type_check typectx apparg f_rty_argty in
        let retty = unify_arr_ret apparg f_rty in
        let () = end_info __LINE__ "App" retty in
        retty
    | CLetE { lhs; rhs; letbody } ->
        let () = before_info __LINE__ "LetE" in
        let rhs_rty = comp_type_infer typectx rhs in
        let binding = R.( #: ) lhs.x rhs_rty in
        let typectx' =
          { typectx with rctx = RCtx.new_to_right typectx.rctx binding }
        in
        let res = comp_type_infer typectx' letbody in
        let res = exists_typed binding res in
        let () = end_info __LINE__ "LetE" res in
        res
    | _ -> _failatwith __FILE__ __LINE__ ""
  in
  rty

and value_type_check { rctx; eqctx } (a : value typed) (rty : R.t) : unit =
  let print_typing_rule line rule =
    print_typing_rule __FILE__ line "CheckValue" rule;
    RCtx.pretty_print_judge rctx (layout_value a, rty)
  in
  let aty = a.ty in
  match a.x with
  | VConst _ | VVar _ ->
      let rty' = value_type_infer rctx a in
      let () = print_typing_rule __LINE__ "Const|Var" in
      let () = subtyping_check rctx rty' rty in
      ()
  | VFix { fixname; fixarg; fixbody } ->
      let () = print_typing_rule __LINE__ "Fix" in
      let self = R.( #: ) fixname.x rty in
      let rctx' = RCtx.new_to_right rctx self in
      let a' = (VLam { lamarg = fixarg; lambody = fixbody }) #: aty in
      value_type_check rctx' a' rty
  | VLam { lamarg; lambody } ->
      let () = print_typing_rule __LINE__ "Lam" in
      let dep, _, rarg, retrty =
        unify_arr_ret (VVar lamarg.x) #: lamarg.ty rty
      in
      let () =
        match dep with R.Pi -> () | _ -> _failatwith __FILE__ __LINE__ "?"
      in
      let lamarg = R.( #: ) lamarg.x rarg.ty in
      let rctx' = RCtx.new_to_right rctx lamarg in
      comp_type_check rctx' lambody retrty
  | _ -> _failatwith __FILE__ __LINE__ ""

and comp_type_check { rctx; eqctx } (a : comp typed) (rty : R.t) : unit =
  let print_typing_rule line rule =
    print_typing_rule __FILE__ line "CheckComp" rule;
    RCtx.pretty_print_judge rctx (layout_comp a, rty)
  in
  let aty = a.ty in
  match a.x with
  | CVal v -> value_type_check rctx v #: aty rty
  | CLetE _ ->
      let rty' = comp_type_infer rctx a in
      let () = print_typing_rule __LINE__ "LetE" in
      subtyping_check rctx rty' rty
  (* | CLetE { lhs; rhs; letbody } -> *)
  (*     let () = print_typing_rule __LINE__ "LetE" in *)
  (*     let rhs_rty = comp_type_infer rctx rhs in *)
  (*     let rctx' = RCtx.new_to_right rctx (R.( #: ) lhs.x rhs_rty) in *)
  (*     comp_type_check rctx' letbody rty *)
  | CIte _ ->
      let rty' = comp_type_infer rctx a in
      let () = print_typing_rule __LINE__ "Ite" in
      subtyping_check rctx rty' rty
  | _ -> _failatwith __FILE__ __LINE__ ""

let check code normalized_code =
  let rctx = RCtx.from_code code in
  let tasks = RCtx.get_task code in
  let () =
    List.iteri
      (fun id (name, rty) ->
        let id = id + 1 in
        let () =
          Env.show_debug_typing @@ fun _ -> Pp.printf "@{<bold>Task %i:@}\n" id
        in
        match
          List.find_opt
            (fun (name', _) -> String.equal name name')
            normalized_code
        with
        | None -> _failatwith __FILE__ __LINE__ ""
        | Some (_, comp) ->
            let _ = comp_type_check rctx comp rty in
            ())
      tasks
  in
  ()
