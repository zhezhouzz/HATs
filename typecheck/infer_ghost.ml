open Language
module P = Rty.P
open Rty
open Sugar

(* let template_subst_lit (phi, prop) prop *)

let xs_names n = List.init n (fun i -> spf "w%i" i)

let find_lits_contain_prop_func prop_func_name lits =
  let vss =
    List.filter_map
      (fun lit ->
        match lit with
        | AAppOp (op, args) when Op.eq op.x (Op.BuiltinOp prop_func_name) ->
            let vs = typed_force_to_id_list args in
            Some vs
        | _ -> None)
      lits
  in
  vss

let unify_prop_func_args prop_func_name lits =
  let vss = find_lits_contain_prop_func prop_func_name lits in
  let vs =
    match vss with
    | [] -> _failatwith __FILE__ __LINE__ "die"
    | [ vs ] -> vs
    | vs :: vss ->
        _assert __FILE__ __LINE__
          "Syntax error: the prop function should be applied over the same set \
           of variables"
        @@ List.for_all (fun vs' -> List.equal String.equal vs vs') vss;
        vs
  in
  vs

open Zzdatatype.Datatype

let unify_prop_func_op_args prop_func_name m =
  let l =
    StrMap.filter_map
      (fun opname (_, lits) ->
        let vss = find_lits_contain_prop_func prop_func_name lits in
        match vss with [] -> None | vs :: _ -> Some (opname, vs)
        (* | _ -> *)
        (*     _failatwith __FILE__ __LINE__ *)
        (* "Syntax error: the prop function should be applied once in a \ *)
           (*        qualifer" *))
      m
  in
  let l = StrMap.to_value_list l in
  let op_vs =
    match l with
    | [] -> _failatwith __FILE__ __LINE__ "die"
    | [ (op, vs) ] -> (op, vs)
    | (op, vs) :: vss ->
        _assert __FILE__ __LINE__
          "Syntax error: the prop function should be applied over the same set \
           of variables and works on only one event"
        @@ List.for_all
             (fun (op', vs') ->
               String.equal op op' && List.equal String.equal vs vs')
             vss;
        (op, vs)
  in
  op_vs

let get_local_fv vs lit =
  let fvs = typed_fv_lit lit #: Nt.Ty_bool in
  List.filter (fun x -> List.exists (fun y -> String.equal x.x y.x) vs) fvs

let gather_op_vs_related_lits m prop_func_name vs =
  let l =
    StrMap.filter_map
      (fun _ (localvs, lits) ->
        let lits =
          List.filter_map
            (fun lit ->
              match lit with
              | AAppOp (op, _) when Op.eq op.x (Op.BuiltinOp prop_func_name) ->
                  None
              | _ ->
                  let fvs = get_local_fv localvs lit in
                  if List.length fvs == List.length vs then
                    (* HACK: only when it has one fv *)
                    let () =
                      _assert __FILE__ __LINE__ "only when it has one fv"
                        (List.length fvs == 1)
                    in
                    if (List.nth fvs 0).ty == (List.nth vs 0).ty then
                      let tmp = _safe_combine __FILE__ __LINE__ fvs vs in
                      let lit =
                        List.fold_left
                          (fun lit (id1, id2) ->
                            subst_lit_id (id1.x, id2.x) lit)
                          lit tmp
                      in
                      Some lit
                    else None
                  else None)
            lits
        in
        match lits with [] -> None | _ -> Some lits)
      m
  in
  let l = List.concat @@ StrMap.to_value_list l in
  l

type infer_ctx = { ws : string typed list; ftab : prop list }
type solution = PropFunc of { candidate : int list }

let candidate_to_prop ictx candidate =
  let l = List.map (fun idx -> List.nth ictx.ftab idx) candidate in
  match l with [] -> mk_false | _ -> Or l

let layout_solution ictx = function
  | PropFunc { candidate } ->
      let prop = candidate_to_prop ictx candidate in
      layout_prop prop

let layout_solution_raw _ = function
  | PropFunc { candidate } -> IntList.to_string candidate

let solution_instantiate ictx solution lits =
  match solution with
  | PropFunc { candidate } ->
      let prop = candidate_to_prop ictx candidate in
      (* let ws = List.map (fun x -> x.x) ictx.ws in *)
      let bindings = _safe_combine __FILE__ __LINE__ ictx.ws lits in
      List.fold_left
        (fun prop (y, z) -> subst_prop_id (y.x, z) prop)
        prop bindings

let mk_feature_tab lits =
  let rec aux lits =
    match lits with
    | [] -> [ [ Lit mk_lit_true ] ]
    | [ lit ] -> [ [ Lit lit ]; [ Not (Lit lit) ] ]
    | lit :: rs ->
        let res = aux rs in
        let res_t = List.map (fun conjs -> Lit lit :: conjs) res in
        let res_f = List.map (fun conjs -> Not (Lit lit) :: conjs) res in
        res_t @ res_f
  in
  let dnf = aux lits in
  List.map (fun conjs -> And conjs) dnf

let layout_ftab ftab =
  Env.show_debug_info @@ fun _ ->
  Pp.printf "ftab\n";
  List.iteri (fun idx prop -> Pp.printf "%i: %s\n" idx @@ layout_prop prop) ftab

let mk_candidates lits =
  let rec aux ns =
    match ns with
    | [] -> _failatwith __FILE__ __LINE__ "die"
    | [ n ] -> [ [ n ]; [] ]
    | n :: ns ->
        let res = aux ns in
        let res_t = List.map (fun conjs -> n :: conjs) res in
        let res_f = res in
        res_t @ res_f
  in
  let ns = List.init (List.length lits) (fun x -> x) in
  aux ns

open Stat

let stat_record : elrond_stat list ref = ref []
let stat = ref { num_lit = 0; num_fv = 0; num_pos = 0; num_neg = 0 }

let init_stat num_lit num_fv =
  stat := { num_lit; num_fv; num_pos = 0; num_neg = 0 }

let pop_stat () = stat_record := !stat_record @ [ !stat ]
let get_stat () = !stat_record

let mk_ictx gamma prop_func m =
  let argsty, _ = Nt.destruct_arr_tp prop_func.ty in
  let ws_ = xs_names (List.length argsty) in
  let ws =
    List.map (fun (x, ty) -> Nt.{ x; ty })
    @@ _safe_combine __FILE__ __LINE__ ws_ argsty
  in
  (* let op = prop_func.x in *)
  (* let op, ws = unify_prop_func_op_args prop_func_name m in *)
  let lits =
    List.slow_rm_dup eq_lit @@ gather_op_vs_related_lits m prop_func.x ws
  in
  let () =
    Env.show_debug_queries @@ fun _ ->
    Pp.printf "@{<bold>@{<orange>lits: %s@}@}\n"
      (List.split_by_comma layout_lit lits)
  in
  let ftab = mk_feature_tab lits in
  let ftab =
    List.filter
      (fun prop ->
        let ws = List.map (fun x -> x.x #:: (mk_top_pty x.ty)) ws in
        let gamma' = PTypectx.new_to_rights gamma ws in
        let b = Subtyping.is_bot_cty gamma' (mk_unit_cty_from_prop prop) in
        not b)
      ftab
  in
  (* let ftab = if List.length ftab == 0 then [ mk_true ] else ftab in *)
  let () = layout_ftab ftab in
  let () = init_stat (List.length lits) (List.length ftab) in
  (* let () = if 1 < List.length ftab then failwith "end" else () in *)
  { ftab; ws }

type lab = Pos | Neg | NotNeg

let is_not_neg = function Neg -> false | _ -> true

let stat_update_pn tab =
  let num_pos =
    Hashtbl.fold (fun _ lab n -> match lab with Pos -> n + 1 | _ -> n) tab 0
  in
  let num_neg =
    Hashtbl.fold (fun _ lab n -> match lab with Neg -> n + 1 | _ -> n) tab 0
  in
  stat := { !stat with num_neg; num_pos }

let elrond n verifier =
  let pn_tab = Hashtbl.create n in
  let _ = List.init n (fun idx -> Hashtbl.add pn_tab idx NotNeg) in
  let get_current_prop f =
    let fvs =
      Hashtbl.fold (fun fv b l -> if f b then fv :: l else l) pn_tab []
    in
    fvs
  in
  let pick_maybepos () =
    Hashtbl.fold
      (fun fv b res ->
        match res with
        | Some _ -> res
        | None -> ( match b with NotNeg -> Some fv | _ -> None))
      pn_tab None
  in
  let rec loop () =
    match pick_maybepos () with
    | Some fv ->
        let () =
          Env.show_debug_queries @@ fun _ ->
          Pp.printf "@{<bold>@{<orange> pick_maybepos: %i@}@}\n" fv
        in
        let () = Hashtbl.replace pn_tab fv Neg in
        let fvs = get_current_prop is_not_neg in
        if verifier fvs then
          let () =
            Env.show_debug_queries @@ fun _ ->
            Pp.printf "@{<bold>@{<orange> label %i as - @}@}\n" fv
          in
          loop ()
        else
          let () =
            Env.show_debug_queries @@ fun _ ->
            Pp.printf "@{<bold>@{<orange> label %i as + @}@}\n" fv
          in
          Hashtbl.replace pn_tab fv Pos;
          loop ()
    | None ->
        let solution = get_current_prop is_not_neg in
        if verifier solution then Some solution else None
  in
  let res = loop () in
  let () = stat_update_pn pn_tab in
  res

let mk_solution_space ictx =
  let candidates = mk_candidates ictx.ftab in
  let solutions =
    List.map (fun candidate -> PropFunc { candidate }) candidates
  in
  solutions

let template_subst_prop ictx (prop_func_name, solution) prop =
  let rec aux e =
    match e with
    | Lit (AAppOp (op, vs)) when Op.eq op.x (Op.BuiltinOp prop_func_name) ->
        let vs = typed_force_to_id_list vs in
        let prop = solution_instantiate ictx solution vs in
        prop
    | Lit _ -> e
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not e -> Not (aux e)
    | And es -> And (List.map aux es)
    | Or es -> Or (List.map aux es)
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Forall (u, body) -> Forall (u, aux body)
    | Exists (u, body) -> Exists (u, aux body)
  in
  aux prop

let template_subst_sevent ictx (y, z) sevent =
  match sevent with
  | GuardEvent _ -> sevent
  | RetEvent (BasePty { cty = { v; phi } }) ->
      let phi = template_subst_prop ictx (y, z) phi in
      RetEvent (BasePty { cty = { v; phi } })
  | RetEvent _ -> _failatwith __FILE__ __LINE__ "die"
  | EffEvent { op; vs; v; phi } ->
      EffEvent { op; vs; v; phi = template_subst_prop ictx (y, z) phi }

let template_subst_regex ictx (y, z) regex =
  let rec aux regex =
    match regex with
    | AnyA -> AnyA
    | EmptyA -> EmptyA
    | EpsilonA -> EpsilonA
    | EventA se -> EventA (template_subst_sevent ictx (y, z) se)
    | LorA (t1, t2) -> LorA (aux t1, aux t2)
    | SetMinusA (t1, t2) -> SetMinusA (aux t1, aux t2)
    | LandA (t1, t2) -> LandA (aux t1, aux t2)
    | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
    | StarA t -> StarA (aux t)
    | ComplementA t -> ComplementA (aux t)
  in
  aux regex

let solution_size = function PropFunc { candidate } -> List.length candidate
let solution_compare s1 s2 = compare (solution_size s1) (solution_size s2)

let best_solution l =
  match List.destruct_opt @@ List.sort solution_compare l with
  | None -> None
  | Some (x, _) -> Some x

let infer_prop_func gamma previousA (prop_func, templateA) postreg =
  let gathered =
    gathered_rm_dup @@ gather_from_regex (LorA (previousA, templateA))
  in
  let runtime, ictx =
    Sugar.clock (fun () -> mk_ictx gamma prop_func gathered.local_lits)
  in
  let () =
    Env.show_debug_debug @@ fun _ ->
    Pp.printf "@{<bold>Infer_ghost.mk_ictx: @}%f\n" runtime
  in
  let verifier fvs =
    let solution = PropFunc { candidate = fvs } in
    let () =
      Env.show_debug_info @@ fun _ ->
      Pp.printf "@{<bold>@{<orange>Check Solution: @}@}%s\n"
      @@ layout_solution_raw ictx solution
    in
    let specA = template_subst_regex ictx (prop_func.x, solution) templateA in
    let () =
      Env.show_debug_info @@ fun _ ->
      Pp.printf "%s @{<bold><:@} %s\n" (layout_regex previousA)
        (layout_regex specA)
    in
    let res =
      Baux._subtyping_pre_regex_bool gamma (previousA, specA)
      (* Subtyping.sub_pre_regex_bool gamma (previousA, specA)) *)
    in
    (* let () = *)
    (*   Env.show_debug_stat @@ fun _ -> *)
    (*   Pp.printf "@{<bold>subtyping_pre_regex_bool: @}%f\n" runtime *)
    (* in *)
    res
  in
  let runtime, candidate =
    Sugar.clock (fun () -> elrond (List.length ictx.ftab) verifier)
  in
  let () =
    Env.show_debug_debug @@ fun _ ->
    Pp.printf "@{<bold>Infer_ghost.elrond: @}%f\n" runtime
  in
  let () = pop_stat () in
  (* let () = failwith "end" in *)
  let res =
    match candidate with
    | None -> None
    | Some candidate ->
        let solution = PropFunc { candidate } in
        let () =
          Env.show_debug_info @@ fun _ ->
          Pp.printf "@{<bold>@{<orange>Final Solution: @}@}%s\n"
          @@ layout_solution_raw ictx solution
        in
        let postreg =
          template_subst_regex ictx (prop_func.x, solution) postreg
        in
        Some postreg
  in
  res
