open Language
module RCtx = RTypectx
module R = Rty
module P = Rty.P
module ECtx = Eqctx
module ROpCtx = ROpTypectx
open TypedCoreEff
open Sugar

let layout_comp = Denormalize.layout_comp
let layout_value = Denormalize.layout_value

type typectx = { eqctx : ECtx.ctx; rctx : RCtx.ctx; opctx : ROpCtx.ctx }

let print_typectx typectx =
  Env.show_debug_typing (fun () ->
      (* Pp.printf "@{<bold>E:@} %s\n" "omitted"; *)
      (* Pp.printf "@{<bold>Op:@} %s\n" "omitted"; *)
      Pp.printf "@{<bold>R:@} %s\n"
        (RCtx.layout_typed_l (fun x -> x) typectx.rctx))

let print_subtyping typectx (t1, t2) =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>Subtyping:@}\n";
      Pp.printf "@{<bold>R:@} %s\n"
        (RCtx.layout_typed_l (fun x -> x) typectx.rctx);
      Pp.printf "⊢ @{<hi_magenta>%s@}\n<:@{<cyan>%s@}\n" (R.layout_rty t1)
        (R.layout_rty t2))

let print_wellformedness typectx tau =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>WellFormedness:@}\n";
      Pp.printf "@{<bold>R:@} %s\n"
        (RCtx.layout_typed_l (fun x -> x) typectx.rctx);
      Pp.printf "⊢WF @{<hi_magenta>%s@}\n" (R.layout_rty tau))

let print_typing_rule file line funcname rule =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>%s::%s@}(%s:%i)\n" funcname rule file line)

let subtyping_rty_bool file line typectx (t1, t2) =
  let () = Env.show_debug_typing (fun () -> print_subtyping typectx (t1, t2)) in
  if Subtyping.sub_rty_bool typectx.rctx typectx.eqctx t1 t2 then true
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

(* let is_under_unit_top rty = *)
(*   let open R in *)
(*   match rty with *)
(*   | Pty (BasePty { ou = Under; cty = { v; phi } }) -> ( *)
(*       match (v.Nt.ty, get_cbool phi) with *)
(*       | Nt.Ty_unit, Some true -> true *)
(*       | _, _ -> false) *)
(*   | _ -> false *)

(* let simplify_bindings xs = *)
(*   List.filter (fun x -> not (is_under_unit_top x.R.ty)) xs *)

let typectx_new_to_right typectx (binding : string R.typed) =
  if wellformedness_rty_bool typectx binding.ty then
    Some { typectx with rctx = RCtx.new_to_right typectx.rctx binding }
  else None

let typectx_newopt_to_right typectx binding =
  match binding with
  | None -> Some typectx
  | Some binding -> typectx_new_to_right typectx binding

let typectx_new_to_rights typectx (binding : string R.typed list) =
  List.fold_left
    (fun typectx x ->
      let* typectx = typectx in
      typectx_new_to_right typectx x)
    (Some typectx) binding

let multi_exists_typed bindings rty =
  List.fold_right Auxtyping.exists_typed bindings rty

let unify_arr_ret v rty =
  let open R in
  match rty with
  | Pty (ArrPty { rarg; retrty }) -> (
      let lit = _value_to_lit __FILE__ __LINE__ v in
      match rarg.px with
      | None -> (None, retrty)
      | Some x ->
          let retrty = subst (x, lit) retrty in
          (Some x #: (Pty rarg.pty), retrty))
  | _ -> _failatwith __FILE__ __LINE__ ""

let unify_arr_with_var rty v =
  let open R in
  match rty with
  | Pty (ArrPty { rarg; retrty }) -> (
      match rarg.px with
      | None -> (None, retrty)
      | Some x ->
          let retrty = subst_id (x, v) retrty in
          (Some v #: (Pty rarg.pty), retrty))
  | _ -> _failatwith __FILE__ __LINE__ ""

(* let layout_mode = TypeInfer -> "TypeInfer" | TypeCheck -> "TypeCheck" *)
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
        (match rty with None -> "BOT" | Some rty -> R.layout rty))

let print_check_info file line rulename typectx str rty =
  print_typing_rule file line "Check" rulename;
  print_typectx typectx;
  Env.show_debug_typing (fun () ->
      Pp.printf "⊢ @{<hi_magenta>%s@} ⇦"
        (short_str (Env.get_max_printing_size ()) @@ str);
      Pp.printf "@{<cyan>%s@}\n\n" @@ R.layout rty)

let case_cond_mapping =
  [
    ("True", R.mk_pty_var_eq_c Nt.bool_ty (Const.B true));
    ("False", R.mk_pty_var_eq_c Nt.bool_ty (Const.B false));
  ]

let rec value_type_infer typectx (value : value typed) : R.t option =
  let str = layout_value value in
  let before_info line rulename =
    print_infer_info1 __FUNCTION__ line rulename typectx str
  in
  let end_info line rulename rty =
    print_infer_info2 __FUNCTION__ line rulename typectx str rty;
    rty
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
        end_info __LINE__ "Const" (Some rty)
    | VVar x ->
        let () = before_info __LINE__ "Var" in
        let* rty = RCtx.get_ty_opt typectx.rctx x in
        let rty =
          if Nt.is_basic_tp value.ty then
            R.Pty (R.mk_pty_var_eq_var x #: value.ty)
          else rty
        in
        end_info __LINE__ "Var" (Some rty)
    | VTu _ -> _failatwith __FILE__ __LINE__ "unimp"
    | VLam _ | VFix _ ->
        _failatwith __FILE__ __LINE__
          "type synthesis of functions are disallowed"
  in
  rty

and comp_type_infer typectx (comp : comp typed) : R.t option =
  let str = layout_comp comp in
  let before_info line rulename =
    print_infer_info1 __FUNCTION__ line rulename typectx str
  in
  let end_info line rulename rty =
    print_infer_info2 __FUNCTION__ line rulename typectx str rty;
    rty
  in
  let rty =
    match comp.x with
    | CErr ->
        let () = before_info __LINE__ "Err" in
        let res =
          if is_basic_tp comp.ty then Some R.(Pty (R.mk_bot_pty comp.ty))
          else _failatwith __FILE__ __LINE__ "die"
        in
        end_info __LINE__ "Err" res
    | CVal v -> value_type_infer typectx v #: comp.ty
    | CLetE { lhs; rhs; letbody } -> (
        match rhs.x with
        | CApp { appf; apparg } ->
            let () = before_info __LINE__ "LetApp" in
            let res =
              let* (bindings : string R.typed list), rhs_rty =
                app_type_infer typectx appf apparg
              in
              let bindings =
                simplify_bindings @@ bindings @ [ R.( #: ) lhs.x rhs_rty ]
              in
              let* typectx' = typectx_new_to_rights typectx bindings in
              let* res = comp_type_infer typectx' letbody in
              let res = multi_exists_typed bindings res in
              Some res
            in
            end_info __LINE__ "LetApp" res
        | CAppOp { op; appopargs } ->
            let () = before_info __LINE__ "LetAppOp" in
            let res =
              let* (bindings : string R.typed list), rhs_rty =
                appop_type_infer typectx op appopargs
              in
              let bindings =
                simplify_bindings @@ bindings @ [ R.( #: ) lhs.x rhs_rty ]
              in
              let* typectx' = typectx_new_to_rights typectx bindings in
              let* res = comp_type_infer typectx' letbody in
              let res = multi_exists_typed bindings res in
              Some res
            in
            end_info __LINE__ "LetAppOp" res
        | _ ->
            let () = before_info __LINE__ "LetE" in
            let res =
              let* rhs_rty = comp_type_infer typectx rhs in
              let bindings = simplify_bindings @@ [ R.( #: ) lhs.x rhs_rty ] in
              let* typectx' = typectx_new_to_rights typectx bindings in
              let* res = comp_type_infer typectx' letbody in
              let res = multi_exists_typed bindings res in
              Some res
            in
            end_info __LINE__ "LetE" res)
    | CApp { appf; apparg } ->
        let () = before_info __LINE__ "App" in
        let res =
          let* (bindings : string R.typed list), rhs_rty =
            app_type_infer typectx appf apparg
          in
          let res = multi_exists_typed bindings rhs_rty in
          Some res
        in
        end_info __LINE__ "App" res
    | CAppOp { op; appopargs } ->
        let () = before_info __LINE__ "AppOp" in
        let res =
          let* (bindings : string R.typed list), rhs_rty =
            appop_type_infer typectx op appopargs
          in
          let res = multi_exists_typed bindings rhs_rty in
          Some res
        in
        end_info __LINE__ "AppOp" res
    | CMatch { matched; match_cases } ->
        let () = before_info __LINE__ "Match" in
        let res =
          match matched.ty with
          | Nt.Ty_bool -> (
              let tys =
                List.filter_map (handle_match_case typectx matched) match_cases
              in
              match tys with [] -> None | _ -> Some (Auxtyping.disj_rtys tys))
          | _ -> _failatwith __FILE__ __LINE__ ""
        in
        end_info __LINE__ "Match" res
    | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp"
  in
  rty

and handle_match_case typectx matched { constructor; args; exp } =
  let _, fty =
    List.find (fun (x, _) -> String.equal constructor.x x) case_cond_mapping
  in
  let xs, retrty =
    List.fold_left
      (fun (xs, fty) x ->
        let y, fty = unify_arr_with_var fty x.x in
        (xs @ [ y ], fty))
      ([], R.Pty fty) args
  in
  let xs =
    List.filter_map
      R.(
        fun x ->
          match x with
          | Some { x; ty } -> Some { x; ty = rty_flip ty }
          | None -> None)
      xs
  in
  let a =
    let open R in
    match retrty with
    | Pty (BasePty { ou = Under; cty = { v; phi } }) ->
        let lit = _value_to_lit __FILE__ __LINE__ matched in
        let phi = subst_prop (v.Nt.x, lit) phi in
        { x = Rename.unique "a"; ty = mk_unit_under_rty_from_prop phi }
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let bindings = simplify_bindings @@ xs @ [ a ] in
  let* typectx' = typectx_new_to_rights typectx bindings in
  let* res = comp_type_infer typectx' exp in
  let res = multi_exists_typed bindings res in
  Some res

and app_type_infer_aux typectx (f_rty : R.t) (apparg : value typed) :
    (string R.typed list * R.t) option =
  let open R in
  match f_rty with
  | Pty (ArrPty { rarg; retrty }) -> (
      match (rarg.px, rarg.pty) with
      | None, ArrPty _ ->
          let b = value_type_check typectx apparg (Pty rarg.pty) in
          if b then
            (* let typectx = typectx_newopt_to_right typectx binding in *)
            Some ([], retrty)
          else None
      | cx, BasePty { ou = Over; cty = { v; phi } } ->
          let apparg_lit = _value_to_lit __FILE__ __LINE__ apparg in
          let phi = subst_prop (v.Nt.x, apparg_lit) phi in
          let a =
            { x = Rename.unique "a"; ty = mk_unit_under_rty_from_prop phi }
          in
          let retrty =
            match cx with
            | None -> retrty
            | Some cx -> subst (cx, apparg_lit) retrty
          in
          Some ([ a ], retrty)
      | _ -> _failatwith __FILE__ __LINE__ "die")
  | _ -> _failatwith __FILE__ __LINE__ "die"

and app_type_infer typectx (appf : value typed) (apparg : value typed) :
    (string R.typed list * R.t) option =
  let* bindings, res =
    let* f_rty = value_type_infer typectx appf in
    app_type_infer_aux typectx f_rty apparg
  in
  Some (bindings, res)

and multi_app_type_infer_aux typectx (f_rty : R.t) (appargs : value typed list)
    : (string R.typed list * R.t) option =
  List.fold_left
    (fun r apparg ->
      let* bindings, f_rty = r in
      let* bindings', f_rty' = app_type_infer_aux typectx f_rty apparg in
      Some (bindings @ bindings', f_rty'))
    (Some ([], f_rty))
    appargs

and appop_type_infer typectx (op : Op.t typed) (appopargs : value typed list) :
    (string R.typed list * R.t) option =
  match op.x with
  | Op.EffOp effname ->
      let argsnt, retnt = Nt.destruct_arr_tp op.ty in
      let vs = R.vs_names (List.length argsnt) in
      let vs =
        List.map (fun (x, ty) -> { x; ty })
        @@ _safe_combine __FILE__ __LINE__ vs argsnt
      in
      let args = List.map (_value_to_lit __FILE__ __LINE__) appopargs in
      let props =
        List.map (fun (x, lit) ->
            let open P in
            let x_lit = AVar x.x in
            match x.ty with
            | Nt.Ty_bool -> Iff (Lit x_lit, Lit lit)
            | Nt.Ty_int -> Lit (mk_int_l1_eq_l2 x_lit lit)
            | _ -> _failatwith __FILE__ __LINE__ "die")
        @@ _safe_combine __FILE__ __LINE__ vs args
      in
      let regex =
        R.(EventA (EffEvent { op = effname; vs; phi = P.And props }))
      in
      Some ([], R.Regty regex #: retnt)
  | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "use +1 for S and 0 for O"
  | Op.BuiltinOp _ -> (
      match ROpCtx.get_ty_opt typectx.opctx op.x with
      | None ->
          _failatwith __FILE__ __LINE__
            (spf "die: rty of the built-in operation %s is missing"
               (Op.to_string op.x))
      | Some f_rty ->
          let* bindings, res =
            multi_app_type_infer_aux typectx f_rty appopargs
          in
          Some (bindings, res))

and value_type_check typectx (value : value typed) (rty : R.t) : bool =
  let str = layout_value value in
  let before_info line rulename =
    print_check_info __FUNCTION__ line rulename typectx str rty
  in
  let end_info line rulename b =
    print_typing_rule __FUNCTION__ line "Check"
      (spf "%s [%s]" rulename (if b then "✓" else "𐄂"));
    b
  in
  match value.x with
  | VConst _ ->
      let () = before_info __LINE__ "Const" in
      let b =
        match value_type_infer typectx value with
        | None -> false
        | Some rty' -> subtyping_rty_bool __FILE__ __LINE__ typectx (rty', rty)
      in
      end_info __LINE__ "Const" b
  | VVar _ ->
      let () = before_info __LINE__ "Var" in
      let b =
        match value_type_infer typectx value with
        | None -> false
        | Some rty' -> subtyping_rty_bool __FILE__ __LINE__ typectx (rty', rty)
      in
      end_info __LINE__ "Var" b
  | VFix { fixname; fixarg; fixbody } ->
      let () = before_info __LINE__ "Fix" in
      let typectx' =
        match typectx_new_to_right typectx (R.( #: ) fixname.x rty) with
        | Some x -> x
        | None -> _failatwith __FILE__ __LINE__ "die"
      in
      let value' = (VLam { lamarg = fixarg; lambody = fixbody }) #: value.ty in
      let b = value_type_check typectx' value' rty in
      end_info __LINE__ "Fix" b
  | VLam { lamarg; lambody } ->
      let () = before_info __LINE__ "Lam" in
      let rarg, retrty = unify_arr_ret (VVar lamarg.x) #: lamarg.ty rty in
      let rarg =
        let* rarg = rarg in
        Some R.((fun _ -> lamarg.Nt.x) #-> rarg)
      in
      let b =
        match typectx_newopt_to_right typectx rarg with
        | None -> false
        | Some typectx' -> comp_type_check typectx' lambody retrty
      in
      end_info __LINE__ "Lam" b
  | VTu _ -> _failatwith __FILE__ __LINE__ "die"

and comp_type_check typectx (comp : comp typed) (rty : R.t) : bool =
  let str = layout_comp comp in
  let before_info line rulename =
    print_check_info __FUNCTION__ line rulename typectx str rty
  in
  let end_info line rulename b =
    print_typing_rule __FUNCTION__ line "Check"
      (spf "%s <%s>" rulename (if b then "✓" else "𐄂"));
    b
  in
  match comp.x with
  | CVal v -> value_type_check typectx v #: comp.ty rty
  | CLetE _ | CAppOp _ | CApp _ | CLetDeTu _ | CMatch _ | CErr ->
      let () = before_info __LINE__ "Sub" in
      let res = comp_type_infer typectx comp in
      let b =
        match res with
        | None -> false
        | Some rty' -> subtyping_rty_bool __FILE__ __LINE__ typectx (rty', rty)
      in
      end_info __LINE__ "Sub" b
