include Baux
open Language
open TypedCoreEff
open Sugar
open Rty

let app_subst (appf_arg, v) appf_ret =
  match appf_arg.px with
  | None -> appf_ret
  | Some x ->
      let lit = _value_to_lit __FILE__ __LINE__ v in
      subst (x, lit.x) appf_ret

let unify_arr_ret v rty =
  match rty with
  | ArrPty { rarg; retrty; _ } -> (
      let lit = _value_to_lit __FILE__ __LINE__ v in
      match rarg.px with
      | None -> (None, retrty)
      | Some x ->
          let retrty = subst (x, lit.x) retrty in
          (Some x #:: rarg.pty, retrty))
  | _ -> _failatwith __FILE__ __LINE__ ""

(* let unify_arr_with_var_name rty v = *)
(*   let open R in *)
(*   match rty with *)
(*   | Pty (ArrPty { rarg; retrty }) -> ( *)
(*       match rarg.px with *)
(*       | None -> (None, retrty) *)
(*       | Some x -> *)
(*           let retrty = subst_id (x, v) retrty in *)
(*           (Some v #:: rarg.pty, retrty)) *)
(*   | _ -> _failatwith __FILE__ __LINE__ "" *)

(* let layout_mode = TypeInfer -> "TypeInfer" | TypeCheck -> "TypeCheck" *)

let case_cond_mapping =
  [
    ("True", mk_pty_var_eq_c Nt.bool_ty (Const.B true));
    ("False", mk_pty_var_eq_c Nt.bool_ty (Const.B false));
  ]

(* NOTE: The value term can only have pure refinement type (or a type error). *)
let rec value_type_infer typectx (value : value typed) : pty option =
  let str = layout_value value in
  let before_info line rulename =
    print_infer_info1 __FUNCTION__ line rulename typectx str
  in
  let end_info line rulename rty =
    let rty_str =
      let* rty' = rty in
      Some (layout_pty rty')
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
          | Const.U -> unit_pty
          | _ -> mk_pty_var_eq_c value.Nt.ty c
        in
        end_info __LINE__ "Const" (Some rty)
    | VVar x ->
        let () = before_info __LINE__ "Var" in
        let* pty = PCtx.get_ty_opt typectx.rctx x in
        let res =
          match pty with
          | ArrPty _ -> pty
          | BasePty _ -> (
              match erase_pty pty with
              | Nt.Ty_unit -> pty
              | _ -> mk_pty_var_eq_var Nt.(x #: (erase_pty pty)))
          | TuplePty _ -> _failatwith __FILE__ __LINE__ "unimp"
        in
        end_info __LINE__ "Var" (Some res)
    | VTu _ -> _failatwith __FILE__ __LINE__ "unimp"
    | VLam _ | VFix _ ->
        _failatwith __FILE__ __LINE__
          "type synthesis of functions are disallowed"
  in
  rty

(* and comp_type_infer (typectx : typectx) (comp : comp typed) : pty option = *)
(*   let str = layout_comp comp in *)
(*   let before_info line rulename = *)
(*     print_infer_info1 __FUNCTION__ line rulename typectx str *)
(*   in *)
(*   let end_info line rulename rty = *)
(*     let rty_str = *)
(*       let* rty' = rty in *)
(*       Some (layout_pty rty') *)
(*     in *)
(*     print_infer_info2 __FUNCTION__ line rulename typectx str rty_str; *)
(*     rty *)
(*   in *)
(*   let rty = *)
(*     match comp.x with *)
(*     | CErr -> *)
(*         let () = before_info __LINE__ "Err" in *)
(*         let pty = *)
(*           if is_basic_tp comp.ty then mk_bot_pty comp.ty *)
(*           else _failatwith __FILE__ __LINE__ "die" *)
(*         in *)
(*         let res = Some pty in *)
(*         end_info __LINE__ "Err" res *)
(*     | CVal v -> *)
(*         let* pty = value_type_infer typectx v #: comp.ty in *)
(*         Some pty *)
(*     | CAppOp _ | CApp _ -> *)
(*         _failatwith __FILE__ __LINE__ "not in the Monadic Normal Form" *)
(*     | CLetE _ | CMatch _ -> *)
(*         _failatwith __FILE__ __LINE__ *)
(*           "we don't infer type of the let bindings and patten matching" *)
(*     | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp" *)
(*   in *)
(*   rty *)

and value_type_check typectx (value : value typed) (rty : pty) : bool =
  let str = layout_value value in
  let before_info line rulename =
    print_check_info __FUNCTION__ line rulename typectx str (layout_pty rty)
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
      let typectx' = typectx_new_to_right typectx fixname.x #:: rty in
      let value' = (VLam { lamarg = fixarg; lambody = fixbody }) #: value.ty in
      let b = value_type_check typectx' value' rty in
      end_info __LINE__ "Fix" b
  | VLam { lamarg; lambody } ->
      let () = before_info __LINE__ "Lam" in
      let rarg, retrty = unify_arr_ret (VVar lamarg.x) #: lamarg.ty rty in
      let rarg =
        let* rarg = rarg in
        Some (fun _ -> lamarg.Nt.x) #--> rarg
      in
      let typectx' = typectx_newopt_to_right typectx rarg in
      let b = comp_type_check typectx' lambody retrty in
      end_info __LINE__ "Lam" b
  | VTu _ -> _failatwith __FILE__ __LINE__ "die"

and app_type_infer_aux typectx (appf_pty : pty) (apparg : value typed) :
    rty option =
  let appf_arg, appf_ret = pty_destruct_arr appf_pty in
  if value_type_check typectx apparg appf_arg.pty then
    Some (app_subst (appf_arg, apparg) appf_ret)
  else None

(* and split_cases curA x (rhs_rty : rty) = *)
(*   let rhs_regexs = Auxtyping.branchize_regex rhs_rty in *)
(*   let () = _force_not_empty_list __FILE__ __LINE__ rhs_regexs in *)
(*   List.map *)
(*     (fun (curA', pty) -> *)
(*       let curA = Auxtyping.simp @@ SeqA (curA, curA') in *)
(*       (curA, x #:: pty)) *)
(*     rhs_regexs *)

and multi_app_type_infer_aux typectx (f_rty : pty) (appargs : value typed list)
    : rty option =
  List.fold_left
    (fun f_rty apparg ->
      let* f_rty = f_rty in
      let pty = rty_force_pty f_rty in
      app_type_infer_aux typectx pty apparg)
    (Some (Pty f_rty)) appargs

(* and comp_type_check (monadic_ctx : monadic_ctx) (comp : comp typed) (rty : rty) *)
(*   : bool = *)

and split_mctx { typectx; curA; preA } x (rhs_regex : regex) =
  let rhs_regexs = Auxtyping.branchize_regex rhs_regex in
  let () = _force_not_empty_list __FILE__ __LINE__ rhs_regexs in
  List.map
    (fun (curA', pty) ->
      let curA = smart_seq (curA, curA') in
      let typectx = typectx_new_to_right typectx x #:: pty in
      let mctx = { typectx; curA; preA } in
      mctx)
    rhs_regexs

and comp_type_check (typectx : typectx) (comp : comp typed) (rty : rty) : bool =
  match rty with
  | Pty pty ->
      let regex = EventA (RetEvent pty) in
      let mctx = { typectx; preA = EpsilonA; curA = EpsilonA } in
      comp_reg_check mctx comp regex
  | Regty { prereg; postreg; _ } ->
      let mctx = { typectx; preA = prereg; curA = EpsilonA } in
      comp_reg_check mctx comp postreg

and comp_reg_check (mctx : monadic_ctx) (comp : comp typed) (rty : regex) : bool
    =
  let str = layout_comp comp in
  let before_info line rulename =
    print_check_regex_info __FUNCTION__ line rulename mctx str
      (layout_regex rty)
  in
  let end_info line rulename b =
    print_typing_rule __FUNCTION__ line "Check"
      (spf "%s <%s>" rulename (if b then "✓" else "𐄂"));
    b
  in
  let comp_reg_check_letappop mctx (lhs, op, appopargs, letbody) rty =
    let () = before_info __LINE__ "LetAppOp" in
    let f_rty =
      match POpCtx.get_ty mctx.typectx.opctx op.x with
      | [ ty ] -> ty
      | _ -> _failatwith __FILE__ __LINE__ "die"
    in
    let b =
      let* rhs_rty = multi_app_type_infer_aux mctx.typectx f_rty appopargs in
      let rhs_pty = rty_force_pty rhs_rty in
      let mctx' = mctx_new_to_right mctx lhs.x #:: rhs_pty in
      Some (comp_reg_check mctx' letbody rty)
    in
    let b : bool = match b with Some b -> b | None -> false in
    end_info __LINE__ "LetAppOp" b
  in
  let comp_reg_check_letapp mctx (lhs, appf, apparg, letbody) rty =
    let () = before_info __LINE__ "LetApp" in
    let b =
      let* appf_pty = value_type_infer mctx.typectx appf in
      let* rhs_rty = app_type_infer_aux mctx.typectx appf_pty apparg in
      let previousA = smart_seq (mctx.preA, mctx.curA) in
      let* rhs_rty =
        match rhs_rty with
        | Pty pty -> Some (EventA (RetEvent pty))
        | Regty { prereg; postreg; _ } ->
            if
              subtyping_pre_regex_bool __FILE__ __LINE__ mctx.typectx
                (previousA, prereg)
            then Some postreg
            else None
      in
      let mctxs = split_mctx mctx lhs.x rhs_rty in
      let b =
        List.for_all (fun mctx' -> comp_reg_check mctx' letbody rty) mctxs
      in
      Some b
    in
    let b : bool = match b with Some b -> b | None -> false in
    end_info __LINE__ "LetApp" b
  in
  let comp_reg_check_letperform mctx (lhs, opname, appopargs, letbody) rty =
    let () = before_info __LINE__ "LetPerform" in
    (* let () = *)
    (*   Env.show_debug_typing @@ fun _ -> *)
    (*   Printf.printf "Top Operation Ptype Context:\n%s\n\n" *)
    (*   @@ POpTypectx.pretty_layout mctx.typectx.opctx *)
    (* in *)
    let f_rtys = POpCtx.get_ty mctx.typectx.opctx (Op.EffOp opname) in
    let get_b f_rty =
      let* rhs_rty = multi_app_type_infer_aux mctx.typectx f_rty appopargs in
      let previousA = smart_seq (mctx.preA, mctx.curA) in
      let get_rhs_reg () =
        match rhs_rty with
        | Pty
            (ArrPty
              {
                arr_kind = SigamArr;
                rarg;
                retrty = Regty { prereg; postreg; _ };
              }) ->
            let prop_func =
              match rarg.px with
              | None -> _failatwith __FILE__ __LINE__ "die"
              | Some x -> x #: (erase_pty rarg.pty)
            in
            let () =
              Env.show_debug_debug @@ fun _ ->
              Pp.printf "@{<bold>previousA: @}%s\n" (layout_regex previousA)
            in
            let () =
              Env.show_debug_debug @@ fun _ ->
              Pp.printf "@{<bold>prereg: @}%s\n" (layout_regex prereg)
            in
            let runtime, res =
              Sugar.clock (fun () ->
                  Infer_ghost.infer_prop_func mctx.typectx.rctx previousA
                    (prop_func, prereg) postreg)
            in
            let () =
              Env.show_debug_debug @@ fun _ ->
              Pp.printf "@{<bold>Infer_ghost.infer_prop_func: @}%f\n" runtime
            in
            res
        | Regty { prereg; postreg; _ } ->
            if
              subtyping_pre_regex_bool __FILE__ __LINE__ mctx.typectx
                (previousA, prereg)
            then Some postreg
            else None
        | _ -> _failatwith __FILE__ __LINE__ "die"
      in
      let runtime, rhs_reg = Sugar.clock get_rhs_reg in
      let () =
        Env.show_debug_debug @@ fun _ ->
        Pp.printf "@{<bold>comp_reg_check_letperform::get_rhs_reg: @}%f\n"
          runtime
      in
      let* rhs_reg = rhs_reg in
      (* let rhs_cty = pty_to_cty @@ regex_to_pty rhs_reg in *)
      let lits = List.map (_value_to_lit __FILE__ __LINE__) appopargs in
      let rhs_reg =
        SeqA
          ( EventA (mk_effevent_from_application_with_var (opname, lits) lhs),
            rhs_reg )
      in
      let mctxs = split_mctx mctx lhs.x rhs_reg in
      let mctx' =
        match mctxs with [ x ] -> x | _ -> _failatwith __FILE__ __LINE__ "die"
      in
      Some (comp_reg_check mctx' letbody rty)
    in
    let b =
      List.fold_left
        (fun b f_rty ->
          let () =
            Env.show_debug_typing @@ fun _ ->
            Pp.printf "@{<bold>Try type for (%s): @}%s\n" opname
              (layout_pty f_rty)
          in
          match b with Some true -> Some true | _ -> get_b f_rty)
        None f_rtys
    in
    let b : bool = match b with Some b -> b | None -> false in
    end_info __LINE__ "LetPerform" b
    (* let argsnt, _ = Nt.destruct_arr_tp opty in *)
    (* let vs = vs_names (List.length argsnt) in *)
    (* let vs = *)
    (*   List.map (fun (x, ty) -> { x; ty }) *)
    (*   @@ _safe_combine __FILE__ __LINE__ vs argsnt *)
    (* in *)
    (* let lits = List.map (_value_to_lit __FILE__ __LINE__) appopargs in *)
    (* let props = *)
    (*   List.map (fun (x, lit) -> *)
    (*       let open P in *)
    (*       let x_lit = AVar x.x in *)
    (*       match x.ty with *)
    (*       | Nt.Ty_bool -> Iff (Lit x_lit, Lit lit) *)
    (*       | Nt.Ty_int -> Lit (mk_int_l1_eq_l2 x_lit lit) *)
    (*       | _ -> _failatwith __FILE__ __LINE__ "die") *)
    (*   @@ _safe_combine __FILE__ __LINE__ vs lits *)
    (* in *)
    (* let se = EffEvent { op = opname; vs; phi = P.And props } in *)
    (* let pty = *)
    (*   Auxtyping.decide_ret_pty typectx.eqctx typectx.rctx *)
    (*     (fun _ _ -> true) *)
    (*     curA se comp.ty *)
    (* in *)
    (* let curA = SeqA (curA, EventA se) in *)
    (* let typectx' = typectx_new_to_right typectx lhs.x #:: pty in *)
    (* let b = comp_type_check typectx' curA letbody rty in *)
    (* end_info __LINE__ "LetPerform" b *)
  in
  let handle_match_case mctx (matched, { constructor; args; exp }) rty =
    let _, fty =
      List.find (fun (x, _) -> String.equal constructor.x x) case_cond_mapping
    in
    let xs, retrty =
      List.fold_left
        (fun (xs, fty) x ->
          let argty, retty = pty_destruct_arr @@ rty_force_pty fty in
          let retty =
            match argty.px with
            | None -> retty
            | Some y -> subst_id (y, x.Nt.x) retty
          in
          let x = x.Nt.x #:: argty.pty in
          (xs @ [ x ], retty))
        ([], Pty fty) args
    in
    let { v; phi } = rty_force_cty retrty in
    let matched_lit = _value_to_lit __FILE__ __LINE__ matched in
    let phi = P.subst_prop (v.x, matched_lit.x) phi in
    let a_pty = mk_unit_pty_from_prop phi in
    if subtyping_pty_is_bot_bool __FILE__ __LINE__ mctx.typectx a_pty then
      let () =
        Env.show_debug_typing @@ fun _ ->
        Pp.printf "@{<bold>@{<orange>matched case (%s) is unreachable@}@}\n"
          constructor.x
      in
      true
    else
      let a = (Rename.unique "a") #:: a_pty in
      let mctx' = mctx_new_to_rights mctx (xs @ [ a ]) in
      let b = comp_reg_check mctx' exp rty in
      let () =
        Env.show_debug_typing @@ fun _ ->
        Pp.printf "@{<bold>@{<orange>matched case (%s): %b@}@}\n" constructor.x
          b
      in
      b
  in
  match comp.x with
  | CVal v ->
      let rhs_regexs = Auxtyping.branchize_regex rty in
      List.exists
        (fun (r, pty) ->
          subtyping_regex_bool __FILE__ __LINE__ mctx.typectx (mctx.curA, r)
          && value_type_check mctx.typectx v #: comp.ty pty)
        rhs_regexs
  | CLetE { lhs; rhs; letbody } -> (
      match rhs.x with
      | CVal v ->
          let () = before_info __LINE__ "LetValue" in
          let pty = value_type_infer mctx.typectx v #: comp.ty in
          let b =
            match pty with
            | None -> false
            | Some rhs_pty ->
                let mctx' = mctx_new_to_right mctx lhs.x #:: rhs_pty in
                comp_reg_check mctx' letbody rty
          in
          end_info __LINE__ "LetValue" b
      | CApp { appf; apparg } ->
          comp_reg_check_letapp mctx (lhs, appf, apparg, letbody) rty
      | CAppOp { op; appopargs } -> (
          match op.x with
          | Op.BuiltinOp _ ->
              comp_reg_check_letappop mctx (lhs, op, appopargs, letbody) rty
          | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die"
          | Op.EffOp opname ->
              let runtime, res =
                Sugar.clock (fun () ->
                    comp_reg_check_letperform mctx
                      (lhs, opname, appopargs, letbody)
                      rty)
              in
              let () =
                Env.show_debug_debug @@ fun _ ->
                Pp.printf "@{<bold>comp_reg_check_letperform: @}%f\n" runtime
              in
              res)
      | _ ->
          let () = Printf.printf "ERR:\n%s\n" (layout_comp rhs) in
          _failatwith __FILE__ __LINE__ "die")
  | CMatch { matched; match_cases } ->
      let () = before_info __LINE__ "Match" in
      let b =
        List.for_all
          (fun case -> handle_match_case mctx (matched, case) rty)
          match_cases
      in
      end_info __LINE__ "Match" b
  | CAppOp _ | CApp _ -> _failatwith __FILE__ __LINE__ "not in MNF"
  | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp"
  | CErr ->
      let () = before_info __LINE__ "Err" in
      end_info __LINE__ "Err" false
