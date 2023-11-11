include Baux
open Language
open TypedCoreEff
open Sugar
open Rty

let case_cond_mapping =
  [
    ("True", mk_rty_var_eq_c Nt.bool_ty (Const.B true));
    ("False", mk_rty_var_eq_c Nt.bool_ty (Const.B false));
  ]

(* support one *)

(* NOTE: The value term can only have pure refinement type (or a type error). *)
let rec value_type_infer typectx (value : value typed) : rty option =
  (* let str = layout_value value in *)
  (* let before_info line rulename = *)
  (*   print_infer_info1 __FUNCTION__ line rulename typectx str *)
  (* in *)
  (* let end_info line rulename hty = *)
  (*   let hty_str = *)
  (*     let* hty' = hty in *)
  (*     Some (layout_rty hty') *)
  (*   in *)
  (*   print_infer_info2 __FUNCTION__ line rulename typectx str hty_str; *)
  (*   hty *)
  (* in *)
  let hty =
    match value.x with
    | VConst c ->
        (* let () = before_info __LINE__ "Const" in *)
        let hty =
          match c with
          | Const.U -> unit_rty
          | _ -> mk_rty_var_eq_c value.Nt.ty c
        in
        let res = Some hty in
        res
        (* end_info __LINE__ "Const" res *)
    | VVar x ->
        (* let () = before_info __LINE__ "Var" in *)
        let* rty = RCtx.get_ty_opt typectx.rctx x in
        let res =
          match rty with
          | ArrRty _ -> rty
          | BaseRty _ -> (
              match erase_rty rty with
              | Nt.Ty_unit -> rty
              | _ -> mk_rty_var_eq_var Nt.(x #: (erase_rty rty)))
        in
        Some res
        (* end_info __LINE__ "Var" (Some res) *)
    | VTu _ -> _failatwith __FILE__ __LINE__ "unimp"
    | VLam _ | VFix _ ->
        _failatwith __FILE__ __LINE__
          "type synthesis of functions are disallowed"
  in
  hty
(* and value_op_infer_without_ghost typectx (op : string) (hty: hty) : (typectx * rty) option = *)
(*   let lpre = hty_to_pre hty in *)
(*   let* rty = value_type_infer typectx value in *)
(*   let* (bindings, rty) = ghost_infer typectx lpre rty in *)
(*   let typectx' = typectx_new_to_rights typectx bindings in *)
(*   (typectx', rty) *)

and value_type_check typectx (value : value typed) (hty : rty) : unit option =
  let str = layout_value value in
  let before_info line rulename =
    print_check_info __FUNCTION__ line rulename typectx str (layout_rty hty)
  in
  let end_info line rulename is_valid =
    print_typing_rule __FUNCTION__ line "Check"
      (spf "%s [%s]" rulename
         (match is_valid with Some _ -> "✓" | None -> "𐄂"));
    is_valid
  in
  let end_info_b line rulename b =
    let is_valid = if b then Some () else None in
    end_info line rulename is_valid
  in
  let rec handle_ghost typectx (rty : rty) =
    match rty with
    | ArrRty { arr = GhostArr Nt.{ x; ty }; rethty } ->
        let rulename = "TGhost" in
        let () = before_info __LINE__ rulename in
        let x' = Rename.unique x in
        let rethty = subst_hty_id (x, x') rethty in
        let typectx' = typectx_introduce_gvar typectx x' #:: (mk_top ty) in
        let rty = hty_force_rty rethty in
        let _ = end_info_b __LINE__ rulename true in
        handle_ghost typectx' rty
    | _ -> (typectx, rty)
  in
  let typectx, hty = handle_ghost typectx hty in
  match value.x with
  | VConst _ ->
      (* let rulename = "Const" in *)
      (* let () = before_info __LINE__ rulename in *)
      let b =
        match value_type_infer typectx value with
        | None -> false
        | Some hty' -> subtyping_rty_bool __FILE__ __LINE__ typectx (hty', hty)
      in
      let res = if b then Some () else None in
      res
      (* end_info_b __LINE__ rulename b *)
  | VVar _ ->
      let rulename = "Var" in
      let () = before_info __LINE__ rulename in
      let b =
        match value_type_infer typectx value with
        | None -> false
        | Some hty' -> subtyping_rty_bool __FILE__ __LINE__ typectx (hty', hty)
      in
      end_info_b __LINE__ rulename b
  | VFix { fixname; fixarg; fixbody } ->
      let rulename = "Fix" in
      let () = before_info __LINE__ rulename in
      let typectx' = typectx_new_to_right typectx fixname.x #:: hty in
      let value' = (VLam { lamarg = fixarg; lambody = fixbody }) #: value.ty in
      let res = value_type_check typectx' value' hty in
      end_info __LINE__ rulename res
  | VLam { lamarg; lambody } ->
      let rulename = "Lam" in
      let () = before_info __LINE__ rulename in
      let rarg, rethty = unify_var_func_rty lamarg.x hty in
      let typectx' = typectx_newopt_to_right typectx rarg in
      let res = comp_type_check typectx' lambody rethty in
      end_info __LINE__ rulename res
  | VTu _ -> _failatwith __FILE__ __LINE__ "die"

(* and app_type_infer_aux typectx (hty : rty) (apparg : value typed) : *)
(*     (typectx option * hty) option = *)
(*   let arr, rethty = rty_destruct_arr __FILE__ __LINE__ hty in *)
(*   match arr with *)
(*   | NormalArr x -> *)
(*       let* () = value_type_check typectx apparg x.rty in *)
(*       Some (None, snd @@ app_v_arr_ret apparg (arr, rethty)) *)
(*   | GhostArr { x; ty } -> *)
(*       let typectx' = typectx_new_to_right typectx { rx = x; rty = mk_top ty } in *)
(*       (\* _failatwith __FILE__ __LINE__ "unimp" *\) *)
(*       Some (Some typectx', rethty) *)
(*   | ArrArr rty -> *)
(*       let* () = value_type_check typectx apparg rty in *)
(*       Some (None, rethty) *)

and multi_app_type_infer_aux typectx (f_hty : rty) (appargs : value typed list)
    : (typectx * hty) option =
  let rec aux res appargs =
    match appargs with
    | [] -> res
    | apparg :: appargs -> (
        let* typectx, hty = res in
        let rty = hty_force_rty hty in
        let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty in
        match arr with
        | NormalArr x ->
            let () =
              Env.show_log "debug_infer" @@ fun _ ->
              Printf.printf "value_type_check %s <== %s\n" (layout_value apparg)
                (layout_rty x.rty)
            in
            let* () = value_type_check typectx apparg x.rty in
            aux
              (Some (typectx, snd @@ app_v_arr_ret apparg (arr, rethty)))
              appargs
        | GhostArr { x; ty } ->
            let x' = Rename.unique x in
            let rethty = subst_hty_id (x, x') rethty in
            let typectx' =
              typectx_new_to_right typectx { rx = x'; rty = mk_top ty }
            in
            let () =
              Env.show_log "debug_infer" @@ fun _ ->
              Printf.printf "GhostArr ==> ctx: %s\n"
                (RTypectx.layout_typed_l typectx'.rctx)
            in
            aux (Some (typectx', rethty)) (apparg :: appargs)
        | ArrArr rty ->
            let* () = value_type_check typectx apparg rty in
            aux (Some (typectx, rethty)) appargs)
  in
  aux (Some (typectx, Rty f_hty)) appargs

and comp_type_check (typectx : typectx) (comp : comp typed) (hty : hty) :
    unit option =
  match hty with
  | Rty _ | Htriple _ -> comp_htriple_check typectx comp hty
  | Inter (hty1, hty2) ->
      let* () = comp_type_check typectx comp hty1 in
      let* () = comp_type_check typectx comp hty2 in
      Some ()

and comp_htriple_check (typectx : typectx) (comp : comp typed) (hty : hty) :
    unit option =
  let str = layout_comp comp in
  let before_info line rulename =
    print_check_info __FUNCTION__ line rulename typectx str (layout_hty hty)
  in
  let end_info line rulename is_valid =
    print_typing_rule __FUNCTION__ line "Check"
      (spf "%s [%s]" rulename
         (match is_valid with Some _ -> "✓" | None -> "𐄂"));
    is_valid
  in
  let is_new_adding (pre, post) =
    match post with
    | SeqA (post1, post2) -> if eq pre post1 then Some post2 else None
    | _ -> None
  in
  let let_aux typectx (lhs, rhs_hty) letbody hty =
    let rec aux rhs_hty =
      match (rhs_hty, hty) with
      | Rty rty, _ ->
          let typectx' = typectx_new_to_right typectx { rx = lhs.x; rty } in
          comp_htriple_check typectx' letbody hty
      | ( Htriple { pre = pre'; resrty = rty; post = post' },
          Htriple { pre; resrty; post } ) ->
          let typectx' = typectx_new_to_right typectx { rx = lhs.x; rty } in
          let pre =
            match is_new_adding (pre', post') with
            | Some newadding ->
                let () =
                  Env.show_debug_typing @@ fun _ ->
                  Pp.printf "@{<bold>@{<orange>newadding:@}@} %s\n"
                    (layout_regex newadding)
                in
                SeqA (LandA (pre, pre'), newadding)
            | None ->
                let res = LandA (SeqA (pre, StarA AnyA), post') in
                let () =
                  Env.show_debug_typing @@ fun _ ->
                  Pp.printf "@{<bold>@{<orange>with pre:@}@} %s\n"
                    (layout_regex res)
                in
                res
          in
          comp_htriple_check typectx' letbody (Htriple { pre; resrty; post })
      | Htriple _, Rty _ -> _failatwith __FILE__ __LINE__ "eff to pure?"
      | Inter (hty1, hty2), _ ->
          let* () = aux hty1 in
          let* () = aux hty2 in
          Some ()
      | _, _ -> _failatwith __FILE__ __LINE__ "die"
    in
    aux rhs_hty
  in
  let comp_htriple_check_letappop rulename typectx (lhs, op, appopargs, letbody)
      hty =
    let () = before_info __LINE__ rulename in
    let f_rty = ROpCtx.get_ty typectx.opctx op.x in
    let* typectx, f_rty =
      Elim_ghost.force_without_ghost typectx f_rty appopargs hty
    in
    let () =
      Env.show_log "debug_infer" @@ fun _ ->
      Printf.printf "op rty: %s\n" (layout_rty f_rty)
    in
    let* typectx', rhs_hty = multi_app_type_infer_aux typectx f_rty appopargs in
    let () =
      Env.show_log "debug_infer" @@ fun _ ->
      Printf.printf "==> ctx: %s\n" (RTypectx.layout_typed_l typectx'.rctx)
    in
    let res = let_aux typectx' (lhs, rhs_hty) letbody hty in
    end_info __LINE__ rulename res
  in
  let comp_htriple_check_letapppop = comp_htriple_check_letappop "TPOpApp" in
  let comp_htriple_check_letappeop = comp_htriple_check_letappop "TEOpApp" in
  let comp_htriple_check_letapp typectx (lhs, appf, apparg, letbody) hty =
    let rulename = "LetApp" in
    let () = before_info __LINE__ rulename in
    (* let () = Printf.printf "before appf_rty\n" in *)
    let* appf_rty = value_type_infer typectx appf in
    (* let () = Printf.printf "appf_rty:%s\n" (layout_rty appf_rty) in *)
    let gvars, appf_rty = destruct_gvars_rty appf_rty in
    let appf_rty =
      match gvars with
      | [] -> appf_rty
      | _ ->
          let gvars_ty = List.map (fun x -> x.ty) gvars in
          let introduced_ty =
            List.map (fun x -> x.ty) typectx.introduced_gvars
          in
          let () =
            Env.show_log "ghost" @@ fun _ ->
            Printf.printf "gvars: %s;\nintroduced_gvars: %s;\nrty: %s\n"
              (layout_typed_l (fun x -> x) gvars)
              (layout_typed_l (fun x -> x) typectx.introduced_gvars)
              (layout_rty appf_rty)
          in
          let () =
            _assert __FILE__ __LINE__ "ghost vars instantiate"
              (List.equal Nt.eq gvars_ty introduced_ty)
          in
          let appf_rty =
            List.fold_left
              (fun rty (x, y) -> subst_rty_id (x.x, y.x) rty)
              appf_rty
              (_safe_combine __FILE__ __LINE__ gvars typectx.introduced_gvars)
          in
          (* let () = *)
          (*   Printf.printf "instansiated rty: %s\n" (layout_rty appf_rty) *)
          (* in *)
          (* let () = failwith "end" in *)
          appf_rty
    in
    match is_multi_args_rty appf_rty with
    | None ->
        let* typectx, appf_rty =
          Elim_ghost.force_without_ghost typectx appf_rty [ apparg ] hty
        in
        let* typectx', rhs_hty =
          multi_app_type_infer_aux typectx appf_rty [ apparg ]
        in
        let res = let_aux typectx' (lhs, rhs_hty) letbody hty in
        end_info __LINE__ rulename res
    | Some (gvars, appf_rty) ->
        let* typectx', rhs_hty =
          multi_app_type_infer_aux typectx appf_rty [ apparg ]
        in
        let rhs_rty = hty_force_rty rhs_hty in
        let rhs_rty = construct_gvars_rty gvars rhs_rty in
        let res = let_aux typectx' (lhs, Rty rhs_rty) letbody hty in
        end_info __LINE__ rulename res
  in
  let handle_match_case typectx (matched, { constructor; args; exp }) hty =
    let _, fty =
      List.find (fun (x, _) -> String.equal constructor.x x) case_cond_mapping
    in
    let xs, rethty =
      List.fold_left
        (fun (xs, fty) x ->
          let value = (VVar x.x) #: x.ty in
          let fty = hty_force_rty fty in
          let rx, retty = app_v_func_rty value fty in
          let xs = match rx with None -> xs | Some x -> xs @ [ x ] in
          (xs, retty))
        ([], Rty fty) args
    in
    let () =
      Env.show_debug_typing @@ fun _ ->
      Printf.printf "rethty: %s\n" (layout_hty rethty)
    in
    let { v; phi } = hty_force_cty rethty in
    let matched_lit = _value_to_lit __FILE__ __LINE__ matched in
    let phi = P.subst_prop (v.x, matched_lit.x) phi in
    let a_rty = mk_unit_rty_from_prop phi in
    if subtyping_rty_is_bot_bool __FILE__ __LINE__ typectx a_rty then
      let () =
        Env.show_debug_typing @@ fun _ ->
        Pp.printf "@{<bold>@{<orange>matched case (%s) is unreachable@}@}\n"
          constructor.x
      in
      Some ()
    else
      let a = (Rename.unique "a") #:: a_rty in
      let typectx' = typectx_new_to_rights typectx (xs @ [ a ]) in
      let res = comp_htriple_check typectx' exp hty in
      let () =
        Env.show_debug_typing @@ fun _ ->
        Pp.printf "@{<bold>@{<orange>matched case (%s): %b@}@}\n" constructor.x
          (match res with Some _ -> true | None -> false)
      in
      res
  in
  match comp.x with
  | CVal v -> (
      match hty with
      | Rty rty -> value_type_check typectx v #: comp.ty rty
      | Htriple { pre; resrty; post } -> (
          match value_type_check typectx { x = v; ty = comp.ty } resrty with
          | None ->
              if subtyping_srl_bool __FILE__ __LINE__ typectx (pre, EmptyA) then
                Some ()
              else None
          | Some () ->
              if subtyping_srl_bool __FILE__ __LINE__ typectx (pre, post) then
                Some ()
              else None)
      | _ -> _failatwith __FILE__ __LINE__ "die")
  | CLetE { lhs; rhs; letbody } -> (
      match rhs.x with
      | CVal v ->
          let rulename = "LetValue" in
          let () = before_info __LINE__ rulename in
          let* rty = value_type_infer typectx v #: comp.ty in
          let typectx' = typectx_new_to_right typectx lhs.x #:: rty in
          let res = comp_htriple_check typectx' letbody hty in
          end_info __LINE__ rulename res
      | CApp { appf; apparg } ->
          comp_htriple_check_letapp typectx (lhs, appf, apparg, letbody) hty
      | CAppOp { op; appopargs } -> (
          match op.x with
          | Op.BuiltinOp _ ->
              comp_htriple_check_letapppop typectx
                (lhs, op, appopargs, letbody)
                hty
          | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die"
          | Op.EffOp _ ->
              let runtime, res =
                Sugar.clock (fun () ->
                    comp_htriple_check_letappeop typectx
                      (lhs, op, appopargs, letbody)
                      hty)
              in
              let () =
                Env.show_debug_debug @@ fun _ ->
                Pp.printf "@{<bold>comp_htriple_check_letperform: @}%f\n"
                  runtime
              in
              res)
      | _ ->
          let () = Printf.printf "ERR:\n%s\n" (layout_comp rhs) in
          _failatwith __FILE__ __LINE__ "die")
  | CMatch { matched; match_cases } ->
      let () = before_info __LINE__ "Match" in
      let res =
        List.fold_left
          (fun res case ->
            let* () = res in
            handle_match_case typectx (matched, case) hty)
          (Some ()) match_cases
      in
      end_info __LINE__ "Match" res
  | CAppOp _ | CApp _ -> _failatwith __FILE__ __LINE__ "not in MNF"
  | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp"
  | CErr ->
      let () = before_info __LINE__ "Err" in
      end_info __LINE__ "Err" None
