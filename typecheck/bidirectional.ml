include Baux
open Language
open TypedCoreEff
open Sugar

let app_subst (appf_arg, v) appf_ret =
  let open R in
  match appf_arg.px with
  | None -> appf_ret
  | Some x ->
      let lit = _value_to_lit __FILE__ __LINE__ v in
      R.subst (x, lit) appf_ret

let unify_arr_ret v rty =
  let open R in
  match rty with
  | ArrPty { rarg; retrty } -> (
      let lit = _value_to_lit __FILE__ __LINE__ v in
      match rarg.px with
      | None -> (None, retrty)
      | Some x ->
          let retrty = subst (x, lit) retrty in
          (Some x #: rarg.pty, retrty))
  | _ -> _failatwith __FILE__ __LINE__ ""

(* let unify_arr_with_var_name rty v = *)
(*   let open R in *)
(*   match rty with *)
(*   | Pty (ArrPty { rarg; retrty }) -> ( *)
(*       match rarg.px with *)
(*       | None -> (None, retrty) *)
(*       | Some x -> *)
(*           let retrty = subst_id (x, v) retrty in *)
(*           (Some v #: rarg.pty, retrty)) *)
(*   | _ -> _failatwith __FILE__ __LINE__ "" *)

(* let layout_mode = TypeInfer -> "TypeInfer" | TypeCheck -> "TypeCheck" *)

let case_cond_mapping =
  [
    ("True", R.mk_pty_var_eq_c Nt.bool_ty (Const.B true));
    ("False", R.mk_pty_var_eq_c Nt.bool_ty (Const.B false));
  ]

(* NOTE: The value term can only have pure refinement type (or a type error). *)
let rec value_type_infer typectx (value : value typed) : R.pty option =
  let str = layout_value value in
  let before_info line rulename =
    print_infer_info1 __FUNCTION__ line rulename typectx str
  in
  let end_info line rulename rty =
    let rty_str =
      let* rty' = rty in
      Some (R.layout_pty rty')
    in
    print_infer_info2 __FUNCTION__ line rulename typectx str rty_str;
    rty
  in
  let rty =
    match value.x with
    | VConst c ->
        let () = before_info __LINE__ "Const" in
        let rty =
          match c with
          | Const.U -> R.unit_pty
          | _ -> R.mk_pty_var_eq_c value.Nt.ty c
        in
        end_info __LINE__ "Const" (Some rty)
    | VVar x ->
        let () = before_info __LINE__ "Var" in
        let* rty = PCtx.get_ty_opt typectx.rctx x in
        end_info __LINE__ "Var" (Some rty)
    | VTu _ -> _failatwith __FILE__ __LINE__ "unimp"
    | VLam _ | VFix _ ->
        _failatwith __FILE__ __LINE__
          "type synthesis of functions are disallowed"
  in
  rty

and comp_type_infer typectx (_ : R.regex) (comp : comp typed) : R.rty option =
  let str = layout_comp comp in
  let before_info line rulename =
    print_infer_info1 __FUNCTION__ line rulename typectx str
  in
  let end_info line rulename rty =
    let rty_str =
      let* rty' = rty in
      Some (R.layout_rty rty')
    in
    print_infer_info2 __FUNCTION__ line rulename typectx str rty_str;
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
    | CVal v ->
        let* pty = value_type_infer typectx v #: comp.ty in
        Some (R.Pty pty)
    | CAppOp _ | CApp _ ->
        _failatwith __FILE__ __LINE__ "not in the Monadic Normal Form"
    | CLetE _ | CMatch _ ->
        _failatwith __FILE__ __LINE__
          "we don't infer type of the let bindings and patten matching"
    | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp"
  in
  rty

and handle_match_case typectx curA (matched, { constructor; args; exp }) rty =
  let _, fty =
    List.find (fun (x, _) -> String.equal constructor.x x) case_cond_mapping
  in
  let xs, retrty =
    List.fold_left
      (fun (xs, fty) x ->
        let argty, retty = R.pty_destruct_arr @@ R.rty_force_pty fty in
        let retty =
          match argty.px with
          | None -> retty
          | Some y -> R.subst_id (y, x.Nt.x) retty
        in
        let x = R.(x.Nt.x #: argty.pty) in
        (xs @ [ x ], retty))
      ([], R.Pty fty) args
  in
  let R.{ v; phi } = R.rty_force_cty retrty in
  let phi = P.subst_prop (v.x, _value_to_lit __FILE__ __LINE__ matched) phi in
  let a = R.((Rename.unique "a") #: (mk_unit_pty_from_prop phi)) in
  let typectx' = typectx_new_to_rights typectx (xs @ [ a ]) in
  comp_type_check typectx' curA exp rty

and value_type_check typectx (value : value typed) (rty : R.pty) : bool =
  let str = layout_value value in
  let before_info line rulename =
    print_check_info __FUNCTION__ line rulename typectx str (R.layout_pty rty)
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
        | Some rty' -> subtyping_pty_bool __FILE__ __LINE__ typectx (rty', rty)
      in
      end_info __LINE__ "Const" b
  | VVar _ ->
      let () = before_info __LINE__ "Var" in
      let b =
        match value_type_infer typectx value with
        | None -> false
        | Some rty' -> subtyping_pty_bool __FILE__ __LINE__ typectx (rty', rty)
      in
      end_info __LINE__ "Var" b
  | VFix { fixname; fixarg; fixbody } ->
      let () = before_info __LINE__ "Fix" in
      let typectx' = typectx_new_to_right typectx (R.( #: ) fixname.x rty) in
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
      let typectx' = typectx_newopt_to_right typectx rarg in
      let b = comp_type_check typectx' R.EpsilonA lambody retrty in
      end_info __LINE__ "Lam" b
  | VTu _ -> _failatwith __FILE__ __LINE__ "die"

and app_type_infer_aux typectx (appf_pty : R.pty) (apparg : value typed) :
    R.rty option =
  let appf_arg, appf_ret = R.pty_destruct_arr appf_pty in
  if value_type_check typectx apparg appf_arg.pty then
    Some (app_subst (appf_arg, apparg) appf_ret)
  else None

and split_cases curA x (rhs_rty : R.rty) =
  let rhs_rtys = Auxtyping.branchize rhs_rty in
  let () = _force_not_empty_list __FILE__ __LINE__ rhs_rtys in
  List.map
    (fun (curA', pty) ->
      let curA = Auxtyping.simp @@ R.SeqA (curA, curA') in
      (curA, R.(x #: pty)))
    rhs_rtys

and multi_app_type_infer_aux typectx (f_rty : R.pty)
    (appargs : value typed list) : R.rty option =
  List.fold_left
    (fun f_rty apparg ->
      let* f_rty = f_rty in
      let pty = R.rty_force_pty f_rty in
      app_type_infer_aux typectx pty apparg)
    (Some (R.Pty f_rty)) appargs

and comp_type_check typectx (curA : R.regex) (comp : comp typed) (rty : R.rty) :
    bool =
  let str = layout_comp comp in
  let before_info line rulename =
    print_check_info __FUNCTION__ line rulename typectx str (R.layout_rty rty)
  in
  let end_info line rulename b =
    print_typing_rule __FUNCTION__ line "Check"
      (spf "%s <%s>" rulename (if b then "✓" else "𐄂"));
    b
  in
  match comp.x with
  | CVal v -> (
      match rty with
      | Pty pty -> value_type_check typectx v #: comp.ty pty
      | _ -> (
          match value_type_infer typectx v #: comp.ty with
          | None -> false
          | Some v_pty ->
              subtyping_rty_bool __FILE__ __LINE__ typectx curA
                (R.pty_to_ret_rty v_pty, rty)))
  | CLetE { lhs; rhs; letbody } -> (
      match rhs.x with
      | CApp { appf; apparg } ->
          let () = before_info __LINE__ "LetApp" in
          let b =
            let* appf_pty = value_type_infer typectx appf in
            let* rhs_rty = app_type_infer_aux typectx appf_pty apparg in
            let cases = split_cases curA lhs.x rhs_rty in
            let b =
              List.for_all
                (fun (curA, x) ->
                  let typectx' = typectx_new_to_right typectx x in
                  comp_type_check typectx' curA letbody rty)
                cases
            in
            Some b
          in
          let b : bool = match b with Some b -> b | None -> false in
          end_info __LINE__ "LetApp" b
      | CAppOp { op; appopargs } -> (
          match op.x with
          | Op.BuiltinOp _ ->
              let f_rty = POpCtx.get_ty typectx.opctx op.x in
              let b =
                let* rhs_rty =
                  multi_app_type_infer_aux typectx f_rty appopargs
                in
                let rhs_pty = R.rty_force_pty rhs_rty in
                let typectx' =
                  typectx_new_to_right typectx R.(lhs.x #: rhs_pty)
                in
                Some (comp_type_check typectx' curA letbody rty)
              in
              let b : bool = match b with Some b -> b | None -> false in
              end_info __LINE__ "LetApp" b
          | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die"
          | Op.EffOp opname ->
              let () = before_info __LINE__ "LetAppOp" in
              let argsnt, _ = Nt.destruct_arr_tp op.ty in
              let vs = R.vs_names (List.length argsnt) in
              let vs =
                List.map (fun (x, ty) -> { x; ty })
                @@ _safe_combine __FILE__ __LINE__ vs argsnt
              in
              let lits = List.map (_value_to_lit __FILE__ __LINE__) appopargs in
              let props =
                List.map (fun (x, lit) ->
                    let open P in
                    let x_lit = AVar x.x in
                    match x.ty with
                    | Nt.Ty_bool -> Iff (Lit x_lit, Lit lit)
                    | Nt.Ty_int -> Lit (mk_int_l1_eq_l2 x_lit lit)
                    | _ -> _failatwith __FILE__ __LINE__ "die")
                @@ _safe_combine __FILE__ __LINE__ vs lits
              in
              let se = R.EffEvent { op = opname; vs; phi = P.And props } in
              let pty = Auxtyping.decide_ret_pty typectx curA se in
              let curA = R.(SeqA (curA, EventA se)) in
              let typectx' = typectx_new_to_right typectx R.(lhs.x #: pty) in
              let b = comp_type_check typectx' curA letbody rty in
              end_info __LINE__ "LetAppOp" b)
      | _ -> _failatwith __FILE__ __LINE__ "die")
  | CAppOp _ | CApp _ -> _failatwith __FILE__ __LINE__ "not in MNF"
  | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp"
  | CMatch { matched; match_cases } ->
      let () = before_info __LINE__ "Match" in
      let b =
        List.for_all
          (fun case -> handle_match_case typectx curA (matched, case) rty)
          match_cases
      in
      end_info __LINE__ "Match" b
  | CErr ->
      let () = before_info __LINE__ "Err" in
      end_info __LINE__ "Err" true
