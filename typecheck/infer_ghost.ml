open Language
module P = Rty.P
open Rty
open Sugar

(* let template_subst_lit (phi, prop) prop *)

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
        match vss with
        | [] -> None
        | [ vs ] -> Some (opname, vs)
        | _ ->
            _failatwith __FILE__ __LINE__
              "Syntax error: the prop function should be applied once in a \
               qualifer")
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

let gather_op_vs_related_lits m prop_func_name (op, vs) =
  let l =
    StrMap.filter_map
      (fun opname (_, lits) ->
        if String.equal opname op then
          let lits =
            List.filter_map
              (fun lit ->
                match lit with
                | AAppOp (op, _) when Op.eq op.x (Op.BuiltinOp prop_func_name)
                  ->
                    None
                | _ ->
                    let fvs = fv_lit lit in
                    if List.length (List.interset String.equal fvs vs) > 0 then
                      Some lit
                    else None)
              lits
          in
          match lits with [] -> None | _ -> Some lits
        else None)
      m
  in
  let l = List.concat @@ StrMap.to_value_list l in
  l

type infer_ctx = { ws : string list; ftab : prop list }
type solution = PropFunc of { candidate : int list }

let candidate_to_prop ictx candidate =
  let l = List.map (fun idx -> List.nth ictx.ftab idx) candidate in
  match l with [] -> mk_false | _ -> Or l

let layout_solution ictx = function
  | PropFunc { candidate } ->
      let prop = candidate_to_prop ictx candidate in
      layout_prop prop

let solution_instantiate ictx solution lits =
  match solution with
  | PropFunc { candidate } ->
      let prop = candidate_to_prop ictx candidate in
      (* let ws = List.map (fun x -> x.x) ictx.ws in *)
      let bindings = _safe_combine __FILE__ __LINE__ ictx.ws lits in
      List.fold_left
        (fun prop (y, z) -> subst_prop_id (y, z) prop)
        prop bindings

let mk_feature_tab lits =
  let rec aux lits =
    match lits with
    | [] -> _failatwith __FILE__ __LINE__ "die"
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

let mk_ictx prop_func_name m =
  let op, ws = unify_prop_func_op_args prop_func_name m in
  let lits = gather_op_vs_related_lits m prop_func_name (op, ws) in
  let ftab = mk_feature_tab lits in
  let () = layout_ftab ftab in
  (* let () = failwith "end" in *)
  { ftab; ws }

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
  | EffEvent { op; vs; phi } ->
      EffEvent { op; vs; phi = template_subst_prop ictx (y, z) phi }

let template_subst_regex ictx (y, z) regex =
  let rec aux regex =
    match regex with
    | AnyA -> AnyA
    | EmptyA -> EmptyA
    | EpsilonA -> EpsilonA
    | EventA se -> EventA (template_subst_sevent ictx (y, z) se)
    | LorA (t1, t2) -> LorA (aux t1, aux t2)
    | LandA (t1, t2) -> LandA (aux t1, aux t2)
    | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
    | StarA t -> StarA (aux t)
    | ComplementA t -> ComplementA (aux t)
  in
  aux regex

let solution_size = function PropFunc { candidate } -> List.length candidate
let solution_compare s1 s2 = compare (solution_size s1) (solution_size s2)

let best_solution l =
  match List.sort solution_compare l with [] -> None | x :: _ -> Some x

let infer_prop_func gamma previousA (prop_func, templateA) postreg =
  let gathered = gather_from_regex (LorA (previousA, templateA)) in
  let ictx = mk_ictx prop_func.x gathered.local_lits in
  let solutions = mk_solution_space ictx in
  let solutions =
    List.filter
      (fun solution ->
        let () =
          Pp.printf "@{<bold>Check Solution: @}%s\n"
          @@ layout_solution ictx solution
        in
        let specA =
          template_subst_regex ictx (prop_func.x, solution) templateA
        in
        let () =
          Pp.printf "%s @{<bold><:@} %s\n" (layout_regex previousA)
            (layout_regex specA)
        in
        let res = Subtyping.sub_pre_regex_bool gamma (previousA, specA) in
        res)
      solutions
  in
  match best_solution solutions with
  | None -> None
  | Some solution ->
      let () =
        Pp.printf "@{<bold>Solution: @}%s\n" @@ layout_solution ictx solution
      in
      let postreg = template_subst_regex ictx (prop_func.x, solution) postreg in
      Some postreg
