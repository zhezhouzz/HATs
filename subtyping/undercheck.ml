open Languages
open Zzdatatype.Datatype
open Abstraction
open Sugar

(* include Litcheck *)
(* module P = Autov.Prop *)
include Checkaux

let current_rec_self : string option = None

(* let value_set_bot (a : NL.value NL.typed) = *)
(*   let open UL in *)
(*   { ty = UT.nt_to_exn_type (snd a.ty); x = Exn } *)

(* let term_set_bot (a : NL.term NL.typed) = *)
(*   let open UL in *)
(*   { ty = UT.nt_to_exn_type (snd a.ty); x = V Exn } *)

(* let reachability_check uctx ty = Reachability_check.reachability_check uctx ty *)
(* let persistence_check uctx ty = Persistence_check.persistence_check uctx ty *)

let rec value_type_infer (uctx : uctx) (a : NL.value NL.typed) :
    MMT.ut_with_copy =
  let aty = a.ty in
  let open UL in
  let open MMT in
  match a.x with
  | NL.Exn -> UtNormal (UT.nt_to_exn_type (snd aty))
  | NL.Var id -> id_type_infer uctx id
  | NL.Lit lit -> UtNormal (lit_type_infer lit)
  | NL.Lam { lamarg = id; lambody = body } -> (
      let typename =
        match fst id.ty with
        | None -> _failatwith __FILE__ __LINE__ "die"
        | Some x -> x
      in
      let idty =
        match Typectx.get_opt uctx.nctx typename with
        | Some (_, idty) -> idty
        | None ->
            _failatwith __FILE__ __LINE__
            @@ spf "cannot find the notation of %s (named %s)" id.x typename
      in
      match idty with
      | Consumed _ | Ut (UtCopy _) ->
          _failatwith __FILE__ __LINE__ "wrong format"
      | Ut (UtNormal idty) ->
          let id = erase_check_mk_id __FILE__ __LINE__ id idty in
          let retty =
            term_type_infer
              {
                uctx with
                ctx =
                  Typectx.ut_force_add_to_right uctx.ctx (id.x, UtNormal id.ty);
              }
              body
          in
          UtNormal (UT.UnderTy_under_arrow { argty = id.ty; retty })
      | Ot idty ->
          let _ =
            _check_equality __FILE__ __LINE__ NT.eq idty.UT.normalty (snd id.ty)
          in
          let retty =
            term_type_infer
              { uctx with ctx = Typectx.ot_add_to_right uctx.ctx (id.x, idty) }
              body
          in
          UtNormal
            (UT.UnderTy_over_arrow { argname = id.x; argty = idty; retty }))
  | NL.Fix _ -> _failatwith __FILE__ __LINE__ "unimp"

and value_type_check (uctx : uctx) (a : NL.value NL.typed) (ty : UT.t) : unit =
  let open UT in
  let result =
    match (a.NL.x, ty) with
    | NL.Exn, _ | NL.Lit _, _ | NL.Var _, _ ->
        let x = value_type_infer uctx a in
        subtyping_check __FILE__ __LINE__ uctx x ty
    | ( NL.Lam { lamarg = id; lambody = body },
        UnderTy_over_arrow { argname; argty; retty } ) ->
        let () =
          match Typectx.get_opt uctx.nctx id.x with
          | Some _ -> _failatwith __FILE__ __LINE__ "die"
          | None -> ()
        in
        let _ =
          _check_equality __FILE__ __LINE__ NTyped.eq argty.normalty
            (snd id.NL.ty)
        in
        let retty = UT.subst_id retty argname id.x in
        term_type_check
          { uctx with ctx = Typectx.ot_add_to_right uctx.ctx (id.x, argty) }
          body retty
    | ( NL.Lam { lamarg = id; lambody = body },
        UnderTy_under_arrow { argty; retty } ) ->
        let () =
          match Nctx.get_opt uctx.nctx id.x with
          | Some _ -> _failatwith __FILE__ __LINE__ "die"
          | None -> ()
        in
        let id = erase_check_mk_id __FILE__ __LINE__ id argty in
        term_type_check
          {
            uctx with
            ctx = Typectx.ut_force_add_to_right uctx.ctx (id.x, UtNormal id.ty);
          }
          body retty
    | NL.Lam _, _ -> _failatwith __FILE__ __LINE__ ""
    | ( NL.Fix { fixname; fstarg; lambody },
        UnderTy_over_arrow { argname; argty; retty } ) ->
        let a = NL.{ x = Rename.unique fstarg.x; ty = fstarg.ty } in
        let _ = erase_check_mk_id __FILE__ __LINE__ a (ot_to_ut argty) in
        let f = erase_check_mk_id __FILE__ __LINE__ fixname ty in
        let prop = make_order_constraint a.x argname (snd fstarg.ty) in
        let f =
          UL.
            {
              x = f.x;
              ty =
                UT.modify_retty
                  (fun _ prop' ->
                    P.conjunct_tope_uprop __FILE__ __LINE__ [ prop; prop' ])
                  f.ty;
            }
        in
        let ctx' = Typectx.ot_add_to_right uctx.ctx (a.x, argty) in
        let ctx'' = Typectx.ut_force_add_to_right ctx' (f.x, UtNormal f.ty) in
        let retty = UT.subst_id retty argname a.x in
        let lambody = NL.subst_id (fstarg.x, a.x) lambody in
        term_type_check { uctx with ctx = ctx'' } lambody retty
    (* let _ = erase_check_mk_id __FILE__ __LINE__ f ty in *)
    (* NOTE: no step 1 (full projection check) any more *)
    (* let _ = full_projection_check uctx ty in *)
    (* let uctx_base = *)
    (*   { *)
    (*     uctx with *)
    (*     ctx = *)
    (*       Typectx.norefinement_force_add_to_right uctx.ctx *)
    (*         { x = f.x; ty = snd @@ f.ty }; *)
    (*   } *)
    (* in *)
    (* let ty_base = right_ty_measure_0 uctx_base ty in *)
    (* let () = *)
    (*   Typectx.pretty_print_judge uctx_base.ctx *)
    (*     (NL.layout_value body, ty_base) *)
    (* in *)
    (* let _ = value_type_check uctx_base body ty_base in *)
    (* (\* let _ = failwith "end" in *\) *)
    (* let uctx_ind = *)
    (*   { *)
    (*     uctx with *)
    (*     ctx = Typectx.ut_force_add_to_right uctx.ctx UL.{ x = f.x; ty }; *)
    (*   } *)
    (* in *)
    (* let ty_ind = right_ty_measure_ind uctx_ind ty in *)
    (* let () = *)
    (*   Typectx.pretty_print_judge uctx_ind.ctx (NL.layout_value body, ty_ind) *)
    (* in *)
    (* let body = value_type_check uctx_ind body ty_ind in *)
    (* { ty; x = Fix ({ x = f.x; ty }, body) } *)
    | NL.Fix _, _ -> _failatwith __FILE__ __LINE__ ""
  in
  result

and handle_let_body (uctx : uctx) rets body target_type : UL.t =
  (* HACK: Why I fail here? *)
  let if_opt = false in
  let opt_infer =
    match (body, rets) with
    | NL.{ x = NL.V { x = NL.Var id; _ }; _ }, [ (id', idty') ]
      when String.equal id.x id' ->
        if if_opt then Some idty' else None
    | _ -> None
  in
  let ctx' = Typectx.ut_force_add_to_rights uctx.ctx rets in
  match target_type with
  | None -> (
      match opt_infer with
      | None ->
          let ty = term_type_infer { uctx with ctx = ctx' } body in
          close_ids rets ty
      | Some inferred -> ut_eq_to_ut_underctx uctx inferred)
  | Some ty -> (
      match opt_infer with
      | None ->
          let () = term_type_check { uctx with ctx = ctx' } body ty in
          close_ids rets ty
      | Some inferred ->
          let () = subtyping_check __FILE__ __LINE__ uctx inferred ty in
          ty)

and handle_lettu (uctx : uctx) (tu, args, body) target_type =
  let args =
    List.map
      (fun arg -> ut_eq_to_ut_underctx uctx @@ value_type_infer uctx arg)
      args
  in
  let tu = erase_check_mk_id __FILE__ __LINE__ tu (UT.UnderTy_tuple args) in
  handle_let_body uctx [ (tu.x, UtNormal tu.ty) ] body target_type

and handle_letdetu (uctx : uctx) (tu, args, body) target_type =
  let tuty = ut_eq_to_ut_underctx uctx @@ value_type_infer uctx tu in
  let rec loop = function
    | [], [] -> []
    | x :: args, ty :: ts ->
        erase_check_mk_id __FILE__ __LINE__ x ty :: loop (args, ts)
    | _ -> _failatwith __FILE__ __LINE__ ""
  in
  let args = loop (args, UT.assume_tuple __FILE__ __LINE__ tuty) in
  handle_let_body uctx
    (List.map (fun x -> (x.UL.x, MMT.UtNormal x.ty)) args)
    body target_type

and handle_letapp_aux (uctx : uctx)
    (fname, fty, (argsty : MMT.ut_with_copy list)) =
  let open UT in
  (* arguments type check *)
  let args = List.map (fun ty -> (Rename.unique "a", ty)) argsty in
  let () =
    Typectx.pretty_print_app_judge fname uctx.ctx (args, Ut (UtNormal fty))
  in
  let rec aux uctx (a, b) : UT.t option =
    match (a, b) with
    | [], retty ->
        Some retty (* let uctx' = handle_consume uctx (args, fty) in *)
    | (x, xty) :: args, UnderTy_over_arrow { argname; argty; retty } ->
        (* NOTE: special application rule *)
        let fvs = UT.fv (ut_eq_to_ut_underctx uctx xty) @ UT.ot_fv argty in
        let b =
          match fvs with
          | [] ->
              if NT.eq NT.Ty_bool (UT.erase (ut_eq_to_ut_underctx uctx xty))
              then
                subtyping_check_bool __FILE__ __LINE__ { uctx with ctx = [] }
                  (UtNormal (ot_to_ut argty))
                  (ut_eq_to_ut_underctx uctx xty)
              else true
          | _ -> true
        in
        if
          b
          && subtyping_check_bool __FILE__ __LINE__ uctx
               (UtNormal (ot_to_ut argty))
               (ut_eq_to_ut_underctx uctx xty)
        then
          let ctx' = Typectx.ut_force_add_to_right uctx.ctx (x, xty) in
          let retty = subst_id retty argname x in
          match aux { uctx with ctx = ctx' } (args, retty) with
          | None -> None
          | Some ty -> Some (close_ids [ (x, xty) ] ty)
        else None
    | (x, xty) :: args, UnderTy_under_arrow { retty; argty } ->
        if subtyping_check_bool __FILE__ __LINE__ uctx xty argty then
          let ctx' = Typectx.ut_force_add_to_right uctx.ctx (x, xty) in
          let () =
            Env.show_debug_info @@ fun _ ->
            Pp.printf "@{<bold>Consume variable %s@}\n" x
          in
          let uctx = { uctx with ctx = Typectx.consume ctx' x } in
          let () = Typectx.pretty_print uctx.ctx in
          aux uctx (args, retty)
        else None
    | _, _ -> _failatwith __FILE__ __LINE__ ""
  in
  aux uctx (args, fty)

and handle_letapp (uctx : uctx)
    (ret, fname, fty, (argsty : MMT.ut_with_copy list), body) target_type =
  let open UL in
  let open UT in
  match
    handle_letapp_aux uctx (fname, fty, (argsty : MMT.ut_with_copy list))
  with
  | None -> make_basic_bot (snd body.NL.ty)
  | Some retty ->
      let ret = erase_check_mk_id __FILE__ __LINE__ ret retty in
      let () =
        Env.show_debug_debug @@ fun _ ->
        Pp.printf "@{<bold>Let LHS:@} %s => %s\n" ret.x
          (UT.pretty_layout ret.ty)
      in
      handle_let_body uctx [ (ret.x, MMT.UtNormal ret.ty) ] body target_type

and handle_letval (uctx : uctx) (lhs, rhs, body) target_type =
  let rhs = value_type_infer uctx rhs in
  (* let lhs = erase_check_mk_id __FILE__ __LINE__ lhs rhs in *)
  handle_let_body uctx [ (lhs.NL.x, rhs) ] body target_type

and handle_ite uctx (cond, e_t, e_f) =
  (* let open UL in *)
  (* let () = *)
  (*   Pp.printf "@{<bold>Before If@}\n"; *)
  (*   Typectx.pretty_print uctx.ctx *)
  (* in *)
  let condty = value_type_infer uctx cond in
  let handle_case b e =
    let ty =
      match condty with
      | UtCopy id ->
          UT.make_basic_from_prop id.ty (fun _ ->
              if b then P.(Lit (AVar id)) else P.(Not (Lit (AVar id))))
      | UtNormal condty ->
          UT.conjunct condty
          @@ UT.make_basic_from_prop NT.Ty_bool (fun x ->
                 P.(if b then bvar_to_prop x else Not (bvar_to_prop x)))
    in
    let cond_id = (Rename.unique "b", MMT.UtNormal ty) in
    let ctx' = Typectx.ut_force_add_to_right uctx.ctx cond_id in
    let ety = term_type_infer { uctx with ctx = ctx' } e in
    close_ids [ cond_id ] ety
  in
  merge_case_tys [ handle_case true e_t; handle_case false e_f ]

and handle_match uctx (matched, cases) =
  let matched =
    NL.(
      match matched.x with
      | Var id -> id
      | _ -> _failatwith __FILE__ __LINE__ "unimp")
  in
  let handle_case NL.{ constructor; args; exp } =
    let argsnty = List.map (fun x -> snd x.NL.ty) args in
    let ftys =
      match argsnty with
      | [] ->
          let fnty = snd matched.NL.ty in
          let matched_rtys =
            Prim.get_primitive_rev_under_ty NL.(constructor.x, fnty)
          in
          List.map
            (fun rty ->
              let basename, normalty, prop =
                UT.assume_base __FILE__ __LINE__ rty
              in
              ( UT.UnderTy_base
                  {
                    basename;
                    normalty;
                    prop = P.subst_id prop basename matched.x;
                  },
                [] ))
            matched_rtys
      | _ ->
          let fnty = NT.(Ty_arrow (snd matched.NL.ty, Ty_tuple argsnty)) in
          let matched_rtys =
            Prim.get_primitive_rev_under_ty NL.(constructor.x, fnty)
          in
          List.map
            (fun rty ->
              match rty with
              | UT.(
                  UnderTy_over_arrow
                    { argname; argty = { basename; normalty; prop }; retty }) ->
                  let matched_rty =
                    UT.UnderTy_base
                      {
                        basename;
                        normalty;
                        prop = P.subst_id prop basename matched.x;
                      }
                  in
                  let matched_argsrty =
                    UT.assume_tuple __FILE__ __LINE__ retty
                  in
                  let matched_argsrty =
                    List.map
                      (fun rty -> UT.subst_id rty argname matched.x)
                      matched_argsrty
                  in
                  (matched_rty, matched_argsrty)
              | _ -> _failatwith __FILE__ __LINE__ "")
            matched_rtys
    in
    let matched_rty, matched_argsrty =
      match ftys with [ fty ] -> fty | _ -> _failatwith __FILE__ __LINE__ ""
    in
    let () =
      Env.show_debug_debug @@ fun _ ->
      Printf.printf "handle_case %s: %s ==> [%s]\n" constructor.x
        (UT.pretty_layout matched_rty)
        (List.split_by_comma UT.pretty_layout matched_argsrty)
    in
    let cond_id = (Rename.unique "b", MMT.UtNormal matched_rty) in
    let matched_args =
      List.map (fun (id, rty) -> (id.NL.x, MMT.UtNormal rty))
      @@ _safe_combine __FILE__ __LINE__ args matched_argsrty
    in
    let ctx' =
      Typectx.ut_force_add_to_rights uctx.ctx (cond_id :: matched_args)
    in
    let ety = term_type_infer { uctx with ctx = ctx' } exp in
    close_ids (cond_id :: matched_args) ety
  in
  let res = List.map handle_case cases in
  merge_case_tys res
(* _failatwith __FILE__ __LINE__ "unimp" *)

and term_type_infer (uctx : uctx) (a : NL.term NL.typed) : UL.t =
  let open NL in
  let bot_res = UT.nt_to_exn_type (snd a.ty) in
  let res =
    match a.x with
    | V v -> ut_eq_to_ut_underctx uctx @@ value_type_infer uctx v
    | LetTu { tu; args; body } -> handle_lettu uctx (tu, args, body) None
    | LetDeTu { tu; args; body } -> handle_letdetu uctx (tu, args, body) None
    | LetOp { ret; op; args; body } ->
        let opty =
          Prim.get_primitive_under_ty
            ( Op.op_to_string op,
              NT.construct_arrow_tp
                (List.map (fun x -> snd x.ty) args, snd ret.ty) )
        in
        let fname = Op.op_to_string op in
        let argsty = List.map (value_type_infer uctx) args in
        handle_letapp uctx (ret, fname, opty, argsty, body) None
    | LetApp { ret; f; args; body } -> (
        let fty =
          try Some (id_type_infer uctx f)
          with FailTypeConsumedonsumed _ -> None
        in
        match fty with
        | None -> bot_res
        | Some (UtCopy _) -> _failatwith __FILE__ __LINE__ ""
        | Some (UtNormal fty) ->
            let argsty = List.map (value_type_infer uctx) args in
            handle_letapp uctx (ret, f.x, fty, argsty, body) None)
    | LetDtConstructor { ret; f; args; body } -> (
        let argsty = List.map (value_type_infer uctx) args in
        let fnty, argsty = dt_expand f argsty in
        (* let argsty = *)
        (*   List.concat *)
        (*   @@ List.map *)
        (*        (fun v -> *)
        (*          let uty = value_type_infer uctx v in *)
        (*          if NT.is_dt (MMT.ut_erase_ uty) then *)
        (*            match uty with *)
        (*            | UtNormal _ -> _failatwith __FILE__ __LINE__ "unimp" *)
        (*            | UtCopy id -> *)
        (*                let sizeargty = *)
        (*                  UT.make_basic_from_prop NT.Ty_int (fun v -> *)
        (*                      P.(MethodPred ("len", [ AVar id; AVar v ]))) *)
        (*                in *)
        (*                [ MMT.UtNormal sizeargty; uty ] *)
        (*          else [ uty ]) *)
        (*        args *)
        (* in *)
        (* let fnty = *)
        (*   let _, retnty = NT.destruct_arrow_tp (snd f.ty) in *)
        (*   let argsnty = List.map MMT.ut_erase_ argsty in *)
        (*   NT.construct_arrow_tp (argsnty, retnty) *)
        (* in *)
        let ftys = Prim.get_primitive_under_multi_ty (f.x, fnty) in
        (* let () = Pp.printf "f: %s; fnty: %s\n" f.x @@ NT.layout fnty in *)
        let tys =
          List.filter_map
            (fun fty -> handle_letapp_aux uctx (f.x, fty, argsty))
            ftys
        in
        (* let () = Pp.printf "%s\n" @@ List.split_by_comma UT.pretty_layout tys in *)
        match tys with
        | [] -> UT.make_basic_bot (snd body.NL.ty)
        | [ retty ] ->
            let ret = erase_check_mk_id __FILE__ __LINE__ ret retty in
            let () =
              Env.show_debug_info @@ fun _ ->
              Pp.printf "@{<bold>Let LHS:@} %s => %s\n" ret.x
                (UT.pretty_layout ret.ty)
            in
            handle_let_body uctx [ (ret.x, MMT.UtNormal ret.ty) ] body None
        | _ ->
            let () =
              List.iter
                (fun fty ->
                  Env.show_debug_info @@ fun _ ->
                  Pp.printf "@{<bold>ALLOWED: %s:@} ==> %s\n" f.x
                    (UT.pretty_layout fty))
                tys
            in
            _failatwith __FILE__ __LINE__ "unimp: still multi")
    | LetVal { lhs; rhs; body } -> handle_letval uctx (lhs, rhs, body) None
    | Ite { cond; e_t; e_f } -> handle_ite uctx (cond, e_t, e_f)
    | Match { matched; cases } -> handle_match uctx (matched, cases)
  in
  let () = Typectx.pretty_print_infer uctx.ctx (NL.layout a, res) in
  res

and term_type_check (uctx : uctx) (x : NL.term NL.typed) (ty : UT.t) : unit =
  let () = Typectx.pretty_print_judge uctx.ctx (NL.layout x, ty) in
  let _ = _check_equality __FILE__ __LINE__ NT.eq (UT.erase ty) (snd @@ x.ty) in
  let open NL in
  match (x.x, ty) with
  | V v, _ -> value_type_check uctx v ty
  | LetTu { tu; args; body }, _ ->
      let _ = handle_lettu uctx (tu, args, body) (Some ty) in
      ()
  | LetDeTu { tu; args; body }, _ ->
      let _ = handle_letdetu uctx (tu, args, body) (Some ty) in
      ()
  | LetApp { ret; f; args; body }, _ -> (
      let fty = id_type_infer uctx f in
      let argsty = List.map (value_type_infer uctx) args in
      match fty with
      | UtCopy _ -> _failatwith __FILE__ __LINE__ ""
      | UtNormal fty ->
          let _ = handle_letapp uctx (ret, f.x, fty, argsty, body) (Some ty) in
          ())
  | LetDtConstructor { ret; f; args; body }, _ -> (
      (* NOTE: add a size before each data type argument *)
      let argsty = List.map (value_type_infer uctx) args in
      let fnty, argsty = dt_expand f argsty in
      let ftys = Prim.get_primitive_under_multi_ty (f.x, fnty) in
      let tys =
        List.filter_map
          (fun fty -> handle_letapp_aux uctx (f.x, fty, argsty))
          ftys
      in
      match tys with
      | [] ->
          subtyping_check __FILE__ __LINE__ uctx
            (MMT.UtNormal (UT.make_basic_bot (snd body.NL.ty)))
            ty
      | [ retty ] ->
          let ret = erase_check_mk_id __FILE__ __LINE__ ret retty in
          let () =
            Env.show_debug_info @@ fun _ ->
            Pp.printf "@{<bold>Let LHS:@} %s => %s\n" ret.x
              (UT.pretty_layout ret.ty)
          in
          let _ =
            handle_let_body uctx [ (ret.x, MMT.UtNormal ret.ty) ] body (Some ty)
          in
          ()
      | _ -> _failatwith __FILE__ __LINE__ "unimp: still multi")
  | LetOp { ret; op; args; body }, _ ->
      let opty =
        Prim.get_primitive_under_ty
          ( Op.op_to_string op,
            NT.construct_arrow_tp (List.map (fun x -> snd x.ty) args, snd ret.ty)
          )
      in
      let fname = Op.op_to_string op in
      let argsty = List.map (value_type_infer uctx) args in
      let _ = handle_letapp uctx (ret, fname, opty, argsty, body) (Some ty) in
      ()
  | LetVal { lhs; rhs; body }, _ ->
      let _ = handle_letval uctx (lhs, rhs, body) (Some ty) in
      ()
  | Ite _, _ | Match _, _ ->
      let x = term_type_infer uctx x in
      Undersub.subtyping_check __FILE__ __LINE__ uctx.ctx x ty

let type_check (uctx : uctx) x ty =
  let res = term_type_check uctx x ty in
  res

module SNA = Languages.StrucNA

let struc_check l notations libs r =
  let open SNA in
  (* let () = *)
  (*   List.iter *)
  (*     (fun (name, ty) -> *)
  (*       Pp.printf "@{<bold>%s@}: %s\n" name @@ UT.pretty_layout ty) *)
  (*     libs *)
  (* in *)
  (* let () = failwith "zz" in *)
  let nctx =
    Typectx.(
      List.fold_left
        (fun ctx (name, ty) -> add_to_right ctx (name, ty))
        empty notations)
  in
  let libctx =
    List.fold_left
      (fun ctx (x, ty) -> Nctx.add_to_right ctx (x, ty))
      Nctx.empty libs
  in
  List.mapi
    (fun id (_, (name', ty)) ->
      let id = id + 1 in
      let () =
        Env.show_debug_typing @@ fun _ -> Pp.printf "@{<bold>Task %i:@}\n" id
      in
      match List.find_opt (fun { name; _ } -> String.equal name name') l with
      | None ->
          _failatwith __FILE__ __LINE__
            (spf "The source code of given refinement type '%s' is missing."
               name')
      | Some { body; _ } ->
          let () =
            Env.show_debug_typing @@ fun _ ->
            Pp.printf "@{<bold>check against with:@} %s\n" (UT.pretty_layout ty)
          in
          let ctx = Typectx.empty in
          let res =
            Undersub.type_err_to_false (fun () ->
                type_check { nctx; ctx; libctx } body ty)
          in
          let () =
            if res then
              Env.show_debug_typing @@ fun _ ->
              Pp.printf "@{<bold>@{<yellow>Task %i, type check succeeded@}@}\n"
                id
            else
              Env.show_debug_typing @@ fun _ ->
              Pp.printf "@{<bold>@{<red>Task %i, type check failed@}@}\n" id
          in
          res)
    r
