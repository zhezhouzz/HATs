open Language
open Rty
open Zzdatatype.Datatype
open Sugar
open Auxtyping

(* let check file line q = *)
(*   match Smtquery.check q with *)
(*   | None ->  *)
(*   | Some m -> *)
(*       (\* let _ = Autov.Func_interp.get_preds_interp m in *\) *)
(*       Smtquery._failwithmodel file line *)
(*         "Subtyping check: rejected by the verifier" m *)

let aux_sub_cty uqvs { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  let open P in
  let phi2 = subst_prop_id (v2.x, v1.x) phi2 in
  let query = multi_forall (v1 :: uqvs, smart_implies phi1 phi2) in
  Smtquery.check query

let sub_cty rctx cty1 cty2 =
  let rec aux rctx uqvs cty1 cty2 =
    match List.last_destruct_opt rctx with
    | None -> aux_sub_cty uqvs cty1 cty2
    | Some (rctx, x) -> (
        let x = typed_force_to_ptyped x in
        match x.pty with
        | TuplePty _ ->
            _failatwith __FILE__ __LINE__ "unimp: tuple type in the ctx"
        | ArrPty _ -> aux rctx uqvs cty1 cty2
        | BasePty { ou = Over; cty } ->
            aux rctx ({ cx = x.px; cty } :: uqvs) cty1 cty2
        | BasePty { ou = Under; _ } ->
            let cty1 = exists_ptyped x cty1 in
            let cty2 = exists_ptyped x cty2 in
            aux rctx uqvs cty1 cty2)
  in
  aux rctx [] cty1 cty2

let rec sub_pty rctx eqctx pty1 pty2 =
  match pty1, pty2 with
  | BasePty {ou = Over; cty = cty1}, BasePty {ou = Under; cty = cty1} ->

let do_check file line (final_uqvs, final_eqvs, final_pre, final_post) =
  (* let () = Printf.printf "_check\n" in *)
  let final_uqvs =
    List.filter
      (fun x -> match x.ty with Ty_unit -> false | _ -> true)
      final_uqvs
  in
  let final_eqvs =
    List.filter
      (fun x -> match x.ty with Ty_unit -> false | _ -> true)
      final_eqvs
  in
  (* if *)
  (*   List.length *)
  (*     (List.filter (fun x -> match x.ty with Ty_unit -> true | _ -> false) *)
  (*     @@ final_uqvs @ final_eqvs) *)
  (*   != 0 *)
  (* then () *)
  (* else *)
  let () =
    let hol_q =
      P.(
        topu_to_prop
          ( final_uqvs,
            tope_to_prop (final_eqvs, Implies (final_pre, final_post)) ))
    in
    match P.fv hol_q with
    | [] -> ()
    | fvs ->
        let () =
          Env.show_debug_info @@ fun _ ->
          Printf.printf "Q: %s\n" (Autov.pretty_layout_prop hol_q)
        in
        _failatwith __FILE__ __LINE__ @@ StrList.to_string fvs
  in
  let pres, uqvs, q =
    with_lemma_to_query (Prim.lemmas_to_pres ())
      (final_uqvs, final_eqvs, final_pre, final_post)
  in
  match
    List.substract String.equal (Autov.prop_fv q) (List.map (fun x -> x.x) uqvs)
  with
  | [] -> check file line pres q
  | fv ->
      let () =
        Env.show_debug_info @@ fun _ ->
        Printf.printf "q: %s\n" @@ Autov.pretty_layout_prop q
      in
      _failatwith __FILE__ __LINE__
        (spf "FV: %s" @@ Zzdatatype.Datatype.StrList.to_string fv)

(* let counter = ref 0 *)

let do_solve_pres pres =
  let rec aux = function
    | (id, ot) :: pres ->
        let ot_uqvs, ot_pre = aux pres in
        (* if List.exists (String.equal id) (P.fv ot_pre @ P.fv target) then *)
        if NT.is_basic_tp ot.UT.normalty then
          let x = { x = id; ty = ot.UT.normalty } in
          let prop = P.subst_id ot.prop ot.basename x.x in
          (x :: ot_uqvs, P.And [ prop; ot_pre ])
        else
          let x = { x = id; ty = ot.UT.normalty } in
          let prop = P.subst_id ot.prop ot.basename x.x in
          (x :: ot_uqvs, P.And [ prop; ot_pre ])
        (* _failatwith __FILE__ __LINE__ "" *)
        (* else (ot_uqvs, ot_pre) *)
    | [] -> ([], P.mk_true)
  in
  let ot_uqvs, ot_pre = aux pres in
  (ot_uqvs, P.peval ot_pre)

let max_uqvs_num = ref 0
let max_eqvs_num = ref 0

let record_max_qvs_num a b =
  let num = List.length b in
  if !a < num then a := num else ()

type destruct_mp = { mp_name : string; intro_tys : NT.t -> NT.t list }

type destruct_ty = {
  elim_ty : Nt.t;
  elim_pre : string -> P.t;
  destruct_mps : destruct_mp list;
}

let make_destruct_mp_prop id { mp_name; intro_tys } =
  let open P in
  let args =
    List.map
      (fun ty -> { x = Rename.unique (spf "%sD" id.x); ty })
      (intro_tys id.ty)
  in
  (mp_name, id, args, mk_mp_vars mp_name (id :: args))

let known_destruct_predicates () =
  let open P in
  let measure = Env.get_measure () in
  let stlc_ty = NT.Ty_constructor ("stlc_ty", []) in
  let stlc_tyctx = NT.Ty_constructor ("stlc_tyctx", []) in
  let stlc_ty_case =
    {
      elim_ty = stlc_ty;
      elim_pre =
        (fun x ->
          let v = { x; ty = stlc_ty } in
          mk_forall (Ty_int, "u") (fun u ->
              Implies
                ( mk_mp_vars measure [ v; u ],
                  MethodPred (">", [ AVar u; ACint 0 ]) )));
      destruct_mps =
        [
          { mp_name = "is_ty_pre"; intro_tys = (fun _ -> [ stlc_ty ]) };
          { mp_name = "is_ty_post"; intro_tys = (fun _ -> [ stlc_ty ]) };
        ];
    }
  in
  let stlc_tyctx_case =
    {
      elim_ty = stlc_tyctx;
      elim_pre =
        (fun x ->
          let v = { x; ty = stlc_tyctx } in
          mk_forall (Ty_int, "u") (fun u ->
              Implies
                ( mk_mp_vars "gamma_size" [ v; u ],
                  MethodPred (">", [ AVar u; ACint 0 ]) )));
      destruct_mps =
        [
          { mp_name = "is_tyctx_hd"; intro_tys = (fun _ -> [ stlc_ty ]) };
          { mp_name = "is_tyctx_tl"; intro_tys = (fun _ -> [ stlc_tyctx ]) };
        ];
    }
  in
  [ stlc_ty_case; stlc_tyctx_case ]

let get_dmps { destruct_mps; _ } = List.map (fun x -> x.mp_name) destruct_mps

let find_dmp_by_type ty cases =
  List.find_opt (fun x -> NT.eq ty x.elim_ty) cases

let build_mapping_from_m m if_conj prop =
  let open P in
  let table = Hashtbl.create 10 in
  let rec aux if_conj t =
    match t with
    | Lit _ -> t
    | Implies (e1, e2) -> Implies (aux (not if_conj) e1, aux if_conj e2)
    | Ite (e1, e2, e3) -> Ite (e1, aux if_conj e2, aux if_conj e3)
    | Not e -> Not (aux (not if_conj) e)
    | And es -> And (List.map (aux if_conj) es)
    | Or es -> Or (List.map (aux (not if_conj)) es)
    | Iff (e1, e2) -> Iff (e1, e2)
    | MethodPred (mp, AVar dt :: args) -> (
        match
          List.find_opt
            (fun ((dmp, id), _) -> String.equal dmp mp && Nt.typed_eq id dt)
            m
        with
        | Some (_, new_args) ->
            let args =
              List.map
                (fun x ->
                  match x with
                  | AVar x -> x
                  | _ -> _failatwith __FILE__ __LINE__ "")
                args
            in
            let ps = List.combine args new_args in
            let () =
              List.iter
                (fun (x, y) ->
                  match Hashtbl.find_opt table x.x with
                  | Some y' when String.equal y.x y' -> ()
                  | Some y' -> _failatwith __FILE__ __LINE__ (spf "y': %s" y')
                  | None -> Hashtbl.add table x.x y.x)
                ps
            in
            if if_conj then P.mk_true else P.mk_false
        | None -> t)
    | MethodPred (_, _) -> t
    | Forall (qv, e) -> Forall (qv, aux if_conj e)
    | Exists (qv, e) -> Exists (qv, aux if_conj e)
  in
  let prop = aux if_conj prop in
  Hashtbl.fold (fun x y prop -> P.subst_id prop x y) table prop

let remove_by_m m if_conj prop =
  let open P in
  let rec aux if_conj t =
    match t with
    | Lit _ -> t
    | Implies (e1, e2) -> Implies (aux (not if_conj) e1, aux if_conj e2)
    | Ite (e1, e2, e3) -> Ite (e1, aux if_conj e2, aux if_conj e3)
    | Not e -> Not (aux (not if_conj) e)
    | And es -> And (List.map (aux if_conj) es)
    | Or es -> Or (List.map (aux (not if_conj)) es)
    | Iff (e1, e2) -> Iff (e1, e2)
    | MethodPred (mp, AVar dt :: _) -> (
        match
          List.find_opt
            (fun ((dmp, id), _) -> String.equal dmp mp && Nt.typed_eq id dt)
            m
        with
        | Some _ -> if if_conj then P.mk_true else P.mk_false
        | None -> t)
    | MethodPred (_, _) -> t
    | Forall (qv, e) -> Forall (qv, aux if_conj e)
    | Exists (qv, e) -> Exists (qv, aux if_conj e)
  in
  aux if_conj prop

let simplify_final_eqvs final_eqvs (final_pre, final_post) =
  List.filter
    (fun qv ->
      List.exists (fun x -> String.equal qv.x x)
      @@ P.fv final_pre @ P.fv final_post)
    final_eqvs

let rlt_instantiate rlt =
  let open P in
  let mk_type_eq_spec (a, b) = mk_mp_vars "type_eq_spec" [ a; b ] in
  let make rlt =
    match rlt with
    | [ (id1, args1); (id2, args2) ] ->
        let matched_p = mk_type_eq_spec (id1, id2) in
        let ps = List.combine args1 args2 in
        (matched_p, List.map mk_type_eq_spec ps)
    | _ -> _failatwith __FILE__ __LINE__ "never happen"
  in
  List.map make @@ List.combination_l rlt 2

let rlt_instantiate2_post prop =
  let open P in
  let rec aux if_conj t =
    match t with
    | Lit _ -> t
    | Implies (e1, e2) -> Implies (aux (not if_conj) e1, aux if_conj e2)
    | Ite (e1, e2, e3) -> Ite (e1, aux if_conj e2, aux if_conj e3)
    | Not e -> Not (aux (not if_conj) e)
    | And es -> And (List.map (aux if_conj) es)
    | Or es -> Or (List.map (aux (not if_conj)) es)
    | Iff (Lit (AVar _), MethodPred ("type_eq_spec", _)) -> mk_true
    | Iff (_, _) -> t
    | MethodPred (mp, AVar dt :: _) ->
        if String.equal mp "is_var_in_range" && not (String.equal dt.x "x") then
          if if_conj then P.mk_true else P.mk_false
        else t
    | MethodPred (_, _) -> t
    | Forall (qv, e) -> Forall (qv, aux if_conj e)
    | Exists (qv, e) -> Exists (qv, aux if_conj e)
  in
  aux true prop

let simplify_by_rlt (pre, post) (matched_p, cases) =
  let open P in
  let table =
    (matched_p, ref None) :: List.map (fun case -> (case, ref None)) cases
  in
  let update p y =
    List.iter
      (fun (p', x) ->
        if strict_eq p p' then
          match !x with
          | None -> x := Some y
          | Some _ -> _failatwith __FILE__ __LINE__ ""
        else ())
      table
  in
  let rec aux t =
    match t with
    | Lit _ -> t
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not e -> Not (aux e)
    | And es -> And (List.map aux es)
    | Or es -> Or (List.map aux es)
    | Iff (Lit (AVar id), p) ->
        update p id;
        mk_true
    | Iff (p, Lit (AVar id)) ->
        update p id;
        mk_true
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | MethodPred (_, _) -> t
    | Forall (qv, e) -> Forall (qv, aux e)
    | Exists (qv, e) -> Exists (qv, aux e)
  in
  let pre = aux pre in
  let post = aux post in
  let id_table = List.filter_map (fun (_, x) -> !x) table in
  if List.length id_table == List.length table then
    match id_table with
    | [] -> _failatwith __FILE__ __LINE__ "never happen"
    | mp :: case_ids ->
        let c =
          Iff (Lit (AVar mp), And (List.map (fun v -> Lit (AVar v)) case_ids))
        in
        (And [ c; pre ], post)
  else (pre, post)

let show_debug_debug str =
  Env.show_debug_debug (fun _ -> Printf.printf "%s" str)

let handle_destruct_predicates (final_uqvs, final_eqvs, final_pre, final_post) =
  let post_mps = P.get_mps final_post in
  let _ =
    Env.show_debug_debug @@ fun _ ->
    Printf.printf "final_uqvs[ZZZZ]: %s\n"
      (List.split_by_comma
         (fun x ->
           spf "%s:%s" x.x (Sexplib.Sexp.to_string @@ NT.sexp_of_t x.ty))
         final_uqvs)
  in
  let cases =
    List.filter
      (fun x ->
        List.length
          (List.interset (fun x y -> String.equal x y.x) (get_dmps x) post_mps)
        > 0)
      (known_destruct_predicates ())
  in
  if List.length cases > 0 then
    let record =
      List.filter_map
        (fun id ->
          match find_dmp_by_type id.ty cases with
          | None -> None
          | Some { elim_pre; destruct_mps; _ } ->
              let pre = elim_pre id.x in
              let constraints =
                List.map (make_destruct_mp_prop id) destruct_mps
              in
              let new_uqvs =
                List.flatten @@ List.map (fun (_, _, qvs, _) -> qvs) constraints
              in
              (* let pres = List.map (fun (_, _, _, prop) -> prop) constraints in *)
              (* let pre = pre :: pres in *)
              let pre = [ pre ] in
              let records =
                List.map (fun (mp, id, args, _) -> ((mp, id), args)) constraints
              in
              let () =
                Env.show_debug_debug @@ fun _ ->
                Printf.printf "new_uqvs: %s\n"
                @@ List.split_by_comma (fun x -> x.x) new_uqvs
              in
              let () =
                Env.show_debug_debug @@ fun _ ->
                Printf.printf "pre: %s\n"
                @@ Autov.pretty_layout_prop (P.And pre)
              in
              Some ((id, new_uqvs, pre), records))
        final_uqvs
    in
    let pres, m = List.split record in
    let rlt, new_uqvs, new_pre =
      List.fold_left
        (fun (rlt, new_uqvs, new_pre) (id, a, b) ->
          ((id, a) :: rlt, a :: new_uqvs, b :: new_pre))
        ([], [], []) pres
    in
    let rlt = rlt_instantiate rlt in
    let () =
      show_debug_debug @@ Printf.sprintf "len(rlt) := %i\n" (List.length rlt)
    in
    let new_uqvs = List.flatten new_uqvs in
    let new_pre = P.And (List.flatten new_pre) in
    let () =
      show_debug_debug
      @@ Printf.sprintf "new_uqvs: %s\n"
      @@ List.split_by_comma (fun x -> x.x) new_uqvs
    in
    let () =
      show_debug_debug @@ Printf.sprintf "pre: %s\n"
      @@ Autov.pretty_layout_prop new_pre
    in
    let final_post = build_mapping_from_m (List.flatten m) true final_post in
    let () =
      show_debug_debug
      @@ Printf.sprintf "final_post: %s\n"
      @@ Autov.pretty_layout_prop final_post
    in
    let final_pre = P.And [ new_pre; final_pre ] in
    let () =
      RTypectx.pretty_print_q
        (List.map (fun x -> x.x) final_uqvs)
        (List.map (fun x -> x.x) final_eqvs)
        final_pre final_post
    in
    (* simplify *)
    let final_pre, final_post =
      List.fold_left simplify_by_rlt (final_pre, final_post) rlt
    in
    let final_post = rlt_instantiate2_post final_post in
    let final_eqvs = simplify_final_eqvs final_eqvs (final_pre, final_post) in
    let final_uqvs =
      simplify_final_eqvs (final_uqvs @ new_uqvs) (final_pre, final_post)
    in
    let () =
      RTypectx.pretty_print_q
        (List.map (fun x -> x.x) final_uqvs)
        (List.map (fun x -> x.x) final_eqvs)
        final_pre final_post
    in
    (final_uqvs, final_eqvs, final_pre, final_post)
  else (final_uqvs, final_eqvs, final_pre, final_post)

let solve_pres file line pres (t1, t2) =
  let name1, nt1, prop1 = UT.assume_base __FILE__ __LINE__ t1 in
  let name2, nt2, prop2 = UT.assume_base __FILE__ __LINE__ t2 in
  let nt = _check_equality __FILE__ __LINE__ NT.eq nt1 nt2 in
  let typeself, prop1, prop2 =
    if String.equal name1 name2 then (name1, prop1, prop2)
    else (name1, P.peval prop1, P.subst_id prop2 name2 name1)
  in
  let ot_uqvs, ot_pre = do_solve_pres pres in
  let prop1 = P.peval prop1 in
  let prop2 = P.peval prop2 in
  let nu = { ty = nt; x = typeself } in
  let () =
    RTypectx.pretty_print_q
      (List.map (fun x -> x.x) ot_uqvs @ [ nu.x ])
      []
      (And [ ot_pre; prop2 ])
      prop1
  in
  let eq2, pre2 = P.assume_tope_uprop __FILE__ __LINE__ prop2 in
  let final_eqvs, final_post =
    P.assume_tope_uprop_fresh_name __FILE__ __LINE__ prop1
  in
  let final_pre = P.And [ ot_pre; pre2 ] in
  let final_uqvs = ot_uqvs @ (nu :: eq2) in
  let () = record_max_qvs_num max_uqvs_num final_uqvs in
  let () = record_max_qvs_num max_eqvs_num final_eqvs in
  do_check file line
    (handle_destruct_predicates (final_uqvs, final_eqvs, final_pre, final_post))

let check_in name t = List.exists (String.equal name) @@ UT.fv t

let check_under_ctx file line ctx (t1, t2) =
  let force_add (id, uty) t1 =
    if UT.is_base_type uty then UT.retty_add_ex_uprop_always_add (id, uty) t1
    else t1
  in
  (* let update_ty_pair (id, uty) (t1, t2) = *)
  (*   let t1 = force_add (id, uty) t1 in *)
  (*   match check_in id t2 with *)
  (*   | false -> *)
  (*       let t2 = force_add (id, uty) t2 in *)
  (*       (t1, t2) *)
  (*   | true -> *)
  (*       let t2 = force_add (id, uty) t2 in *)
  (*       (t1, t2) *)
  (* in *)
  let rec aux pres ctx (t1, t2) =
    match RTypectx.destrct_right ctx with
    | None -> (pres, (t1, t2))
    | Some (ctx, (id, MMT.Ot oty)) -> aux ([ (id, oty) ] @ pres) ctx (t1, t2)
    | Some (ctx, (id, MMT.Consumed (UtCopy id')))
    | Some (ctx, (id, MMT.Ut (UtCopy id'))) ->
        let t1 = UT.subst_id t1 id id'.x in
        let t2 = UT.subst_id t2 id id'.x in
        aux pres ctx (t1, t2)
    | Some (ctx, (id, MMT.Consumed (UtNormal uty)))
    | Some (ctx, (id, MMT.Ut (UtNormal uty))) ->
        let t1 = force_add (id, uty) t1 in
        let t2 = force_add (id, uty) t2 in
        aux pres ctx (t1, t2)
    (* let () = *)
    (* (\*   Printf.printf "simplify_ut: %s : %s\n" id (UT.pretty_layout uty) *\) *)
    (* (\* in *\) *)
    (* (\* let uty = simplify_ut uty in *\) *)
    (* aux pres ctx *)
    (* (update_ty_pair (id, uty) (t1, t2)) *)
  in
  let pres, (t1, t2) = aux [] ctx (t1, t2) in
  solve_pres file line pres (t1, t2)

let subtyping_check_ot_ file line ctx t1 t2 =
  let () =
    Env.show_debug_typing @@ fun _ -> Pp.printf "@{<bold>OVERCHECK@}\n"
  in
  let () = RTypectx.pretty_print_subtyping ctx (MMT.Ot t1, MMT.Ot t2) in
  let () =
    Env.show_debug_typing @@ fun _ ->
    Pp.printf "@{<bold>OVERCHECK Converted@}\n"
  in
  let t1' = UT.ot_to_ut t1 in
  let t2' = UT.ot_to_ut t2 in
  let () =
    RTypectx.pretty_print_subtyping ctx
      (MMT.Ut (MMT.UtNormal t2'), MMT.Ut (MMT.UtNormal t1'))
  in
  check_under_ctx file line ctx (t2', t1')

let subtyping_check_ file line (ctx : RTypectx.ctx) (inferred_ty : UT.t)
    (target_ty : UT.t) =
  let open UT in
  (* let () = if !counter == 1 then failwith "end" else counter := !counter + 1 in *)
  let () =
    RTypectx.pretty_print_subtyping ctx
      (MMT.(Ut (UtNormal inferred_ty)), MMT.(Ut (UtNormal target_ty)))
  in
  let rec aux ctx (t1, t2) =
    match (t1, t2) with
    | UnderTy_base _, UnderTy_base _ -> check_under_ctx file line ctx (t1, t2)
    | UnderTy_tuple ts1, UnderTy_tuple ts2 ->
        List.iter (check_under_ctx file line ctx)
        @@ _safe_combine __FILE__ __LINE__ ts1 ts2
    | ( UnderTy_under_arrow { argty = t11; retty = t12 },
        UnderTy_under_arrow { argty = t21; retty = t22 } ) ->
        aux ctx (t21, t11);
        aux ctx (t12, t22)
    | ( UnderTy_over_arrow { argname = x1; argty = t11; retty = t12 },
        UnderTy_over_arrow { argname = x2; argty = t21; retty = t22 } ) ->
        let () = subtyping_check_ot_ file line ctx t21 t11 in
        let x' = Rename.unique x2 in
        let t12 = subst_id t12 x1 x' in
        let t22 = subst_id t22 x2 x' in
        let ctx = RTypectx.ot_add_to_right ctx (x', t21) in
        aux ctx (t12, t22)
    | _, _ -> _failatwith __FILE__ __LINE__ "die: under subtype"
  in
  aux ctx (inferred_ty, target_ty)

let subtyping_check_counter = ref 0
let subtyping_check_counter_set0 () = subtyping_check_counter := 0

let subtyping_check_counter_plus1 () =
  subtyping_check_counter := !subtyping_check_counter + 1

let subtyping_check file line (ctx : RTypectx.ctx) (inferred_ty : UT.t)
    (target_ty : UT.t) =
  let () = subtyping_check_counter_plus1 () in
  try subtyping_check_ file line ctx inferred_ty target_ty with
  | Autov.FailWithModel (msg, m) ->
      let () =
        Env.show_debug_typing @@ fun _ ->
        Pp.printf "@{<orange>Under Type Check failed:@}%s\n" msg
      in
      raise (FailwithCex (msg, m))
  | Autov.SMTTIMEOUT ->
      let () =
        Env.show_debug_typing @@ fun _ ->
        Pp.printf "@{<orange>Under Type Check failed:@}%s\n" "timeout"
      in
      raise (FailTimeout (__FILE__, __LINE__))
  | e -> raise e

let subtyping_check_ot file line (ctx : RTypectx.ctx) (inferred_ty : UT.ot)
    (target_ty : UT.ot) =
  try subtyping_check_ot_ file line ctx inferred_ty target_ty with
  | Autov.FailWithModel (msg, m) ->
      let () =
        Env.show_debug_typing @@ fun _ ->
        Pp.printf "@{<orange>Over Type Check failed:@}%s\n" msg
      in
      raise (FailwithCex (msg, m))
  | Autov.SMTTIMEOUT ->
      let () =
        Env.show_debug_typing @@ fun _ ->
        Pp.printf "@{<orange>Over Type Check failed:@}%s\n" "timeout"
      in
      raise (FailTimeout (__FILE__, __LINE__))
  | e -> raise e

let type_err_to_false f =
  try
    let _ = f () in
    true
  with
  | FailwithCex _ | FailUnderAgainstOver _ | FailOverAgainstUnder _
  | FailTimeout _ ->
      false
  | FailTypeConsumedonsumed _ ->
      let () =
        Env.show_debug_typing @@ fun _ ->
        Pp.printf "@{<orange>Over Type Check failed:@}%s\n" "consumed"
      in
      false
  | e -> raise e

let subtyping_check_bool file line (ctx : RTypectx.ctx) (inferred_ty : UT.t)
    (target_ty : UT.t) =
  type_err_to_false (fun () ->
      subtyping_check file line ctx inferred_ty target_ty)

let ot_subtyping_check_bool file line (ctx : RTypectx.ctx) (inferred_ty : UT.ot)
    (target_ty : UT.ot) =
  type_err_to_false (fun () ->
      subtyping_check_ot file line ctx inferred_ty target_ty)

let mmt_check file line ctx t1 t2 =
  let open MMT in
  match (t1, t2) with
  | Consumed _, _ -> _err_consumed file line "??"
  | _, Consumed _ -> _err_consumed file line "??"
  | Ut (UtNormal t1), Ut (UtNormal t2) -> subtyping_check file line ctx t1 t2
  | Ut _, Ut _ -> _failatwith __FILE__ __LINE__ "never happen"
  | Ut _, Ot _ -> raise (FailUnderAgainstOver (file, line))
  | Ot _, Ut _ -> raise (FailOverAgainstUnder (file, line))
  | Ot t1, Ot t2 -> subtyping_check_ot file line ctx t1 t2

let mmt_check_bool file line ctx t1 t2 =
  type_err_to_false (fun () -> mmt_check file line ctx t1 t2)
