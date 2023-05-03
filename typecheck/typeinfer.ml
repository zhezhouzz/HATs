open Language
module RCtx = RTypectx
module Nt = Normalty.Ntyped

(* module T = RTypedCoreEff *)
module R = Rty
module P = R.P
open TypedCoreEff

let print_typing_rule file line funcname rule =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>%s::%s@}(%s:%i)\n" funcname rule file line)

let perform_to_trace op lits rty =
  let open R in
  let event = P.(AApp (op, lits)) in
  let new_post =
    mk_basety ty_tr P.(fun v -> Lit (mk_eq ty_tr (AVar v) event))
  in
  match rty with
  | Traced { h; pre; rty; post } ->
      let post = Fexists.exists_base_function (Rename.unique h) post new_post in
      Traced { h; pre; rty; post }
  | _ ->
      Traced
        {
          h = kw_h.x;
          pre = mk_basety ty_tr (fun _ -> P.mk_true);
          rty;
          post = new_post;
        }

open Sugar

let layout_comp = Denormalize.layout_comp
let layout_value = Denormalize.layout_value
let subtyping_check _ _ _ = ()

let rec _value_to_lit file line v =
  let vty = v.ty in
  match v.x with
  | VVar name -> P.AVar name #: vty
  | VConst c -> P.AC c
  | VLam _ -> _failatwith file line "?"
  | VFix _ -> _failatwith file line "?"
  | VHd _ -> _failatwith file line "?"
  | VTu l -> P.ATu (List.map (_value_to_lit file line) l)

let unify_dep v rty =
  let open R in
  match rty with
  | BaseRty _ -> _failatwith __FILE__ __LINE__ ""
  | Traced _ -> _failatwith __FILE__ __LINE__ ""
  | DepRty { dep; label; rarg; retrty } ->
      let retrty =
        match rarg.x with
        | None -> retrty
        | Some x ->
            let lit = _value_to_lit __FILE__ __LINE__ v in
            subst (x, lit) retrty
      in
      (dep, label, rarg, retrty)

let merge_function = Fmerge.merge
let exists_function = Fexists.exists_function

let rec value_type_infer (ctx : RCtx.ctx) (a : value typed) : R.t =
  let aty = a.ty in
  let line_ref, rule_ref = (ref 0, ref "WrongName") in
  let update_typing_rule line rule =
    line_ref := line;
    rule_ref := rule
  in
  let rty =
    match a.x with
    | VConst c ->
        let () = update_typing_rule __LINE__ "Const" in
        let rty =
          match c with Const.U -> R.unit_ty | _ -> R.mk_ubasety_eq_c aty c
        in
        rty
    | VVar x ->
        let () = update_typing_rule __LINE__ "Var" in
        let rty =
          match RCtx.get_ty_opt ctx x with
          | None -> _failatwith __FILE__ __LINE__ "cannot find rty"
          | Some rty -> rty
        in
        if List.length (fst (destruct_arr_tp aty)) == 0 then
          R.mk_ubasety_eq_id aty x
        else rty
    | _ -> _failatwith __FILE__ __LINE__ ""
  in
  let () =
    print_typing_rule __FILE__ !line_ref "InferValue" !rule_ref;
    RCtx.pretty_print_infer ctx (layout_value a, rty)
  in
  rty

and comp_type_infer (ctx : RCtx.ctx) (a : comp typed) : R.t =
  let aty = a.ty in
  let line_ref, rule_ref = (ref 0, ref "WrongName") in
  let update_typing_rule line rule =
    line_ref := line;
    rule_ref := rule
  in
  let rty =
    match a.x with
    | CVal v ->
        let () = update_typing_rule __LINE__ "Val" in
        value_type_infer ctx v #: aty
    | CApp { appf; apparg } ->
        let () = update_typing_rule __LINE__ "App" in
        let f_rty = value_type_infer ctx appf in
        let f_rty_argty = R.get_argty f_rty in
        let () = value_type_check ctx apparg f_rty_argty in
        let _, _, _, retty = unify_dep apparg f_rty in
        retty
    | CIte { cond; et; ef } ->
        let () = update_typing_rule __LINE__ "Ite" in
        let cond_lit = _value_to_lit __FILE__ __LINE__ cond in
        let handle_case b e =
          let tmp_id_ty =
            R.mk_ubasety_eq_lit_lit cond.ty cond_lit (P.AC (Constant.B b))
          in
          let tmp_id = R.( #: ) (Rename.unique "a") tmp_id_ty in
          let ctx' = RCtx.new_to_right ctx tmp_id in
          let ety = comp_type_infer ctx' e in
          exists_function tmp_id ety
        in
        merge_function [ handle_case true et; handle_case false ef ]
    | CLetE { lhs; rhs; letbody } ->
        let () = update_typing_rule __LINE__ "LetE" in
        let rhs_rty = comp_type_infer ctx rhs in
        let binding = R.( #: ) lhs.x rhs_rty in
        let ctx' = RCtx.new_to_right ctx binding in
        let res = comp_type_infer ctx' letbody in
        Fexists.exists_function binding res
    | CAppPerform { effop; appopargs } ->
        let () = update_typing_rule __LINE__ (spf "Perform[%s]" effop.x) in
        let frty =
          match RCtx.get_ty_opt ctx effop.x with
          | None -> _failatwith __FILE__ __LINE__ "cannot find rty"
          | Some rty -> rty
        in
        let retrty =
          List.fold_left
            (fun frty v ->
              let _, _, _, rty = unify_dep v frty in
              rty)
            frty appopargs
        in
        let lits = List.map (_value_to_lit __FILE__ __LINE__) appopargs in
        let retrty = perform_to_trace effop lits retrty in
        retrty
    | _ -> _failatwith __FILE__ __LINE__ ""
  in
  let () =
    print_typing_rule __FILE__ !line_ref "InferComp" !rule_ref;
    RCtx.pretty_print_infer ctx (layout_comp a, rty)
  in
  rty

and value_type_check (ctx : RCtx.ctx) (a : value typed) (rty : R.t) : unit =
  let print_typing_rule line rule =
    print_typing_rule __FILE__ line "CheckValue" rule;
    RCtx.pretty_print_judge ctx (layout_value a, rty)
  in
  let aty = a.ty in
  match a.x with
  | VConst _ | VVar _ ->
      let rty' = value_type_infer ctx a in
      let () = print_typing_rule __LINE__ "Const|Var" in
      let () = subtyping_check ctx rty' rty in
      ()
  | VFix { fixname; fixarg; fixbody } ->
      let () = print_typing_rule __LINE__ "Fix" in
      let self = R.( #: ) fixname.x rty in
      let ctx' = RCtx.new_to_right ctx self in
      let a' = (VLam { lamarg = fixarg; lambody = fixbody }) #: aty in
      value_type_check ctx' a' rty
  | VLam { lamarg; lambody } ->
      let () = print_typing_rule __LINE__ "Lam" in
      let dep, _, rarg, retrty = unify_dep (VVar lamarg.x) #: lamarg.ty rty in
      let () =
        match dep with R.Pi -> () | _ -> _failatwith __FILE__ __LINE__ "?"
      in
      let lamarg = R.( #: ) lamarg.x rarg.ty in
      let ctx' = RCtx.new_to_right ctx lamarg in
      comp_type_check ctx' lambody retrty
  | _ -> _failatwith __FILE__ __LINE__ ""

and comp_type_check (ctx : RCtx.ctx) (a : comp typed) (rty : R.t) : unit =
  let print_typing_rule line rule =
    print_typing_rule __FILE__ line "CheckComp" rule;
    RCtx.pretty_print_judge ctx (layout_comp a, rty)
  in
  let aty = a.ty in
  match a.x with
  | CVal v -> value_type_check ctx v #: aty rty
  | CLetE _ ->
      let rty' = comp_type_infer ctx a in
      let () = print_typing_rule __LINE__ "LetE" in
      subtyping_check ctx rty' rty
  (* | CLetE { lhs; rhs; letbody } -> *)
  (*     let () = print_typing_rule __LINE__ "LetE" in *)
  (*     let rhs_rty = comp_type_infer ctx rhs in *)
  (*     let ctx' = RCtx.new_to_right ctx (R.( #: ) lhs.x rhs_rty) in *)
  (*     comp_type_check ctx' letbody rty *)
  | CIte _ ->
      let rty' = comp_type_infer ctx a in
      let () = print_typing_rule __LINE__ "Ite" in
      subtyping_check ctx rty' rty
  | _ -> _failatwith __FILE__ __LINE__ ""

let check code normalized_code =
  let ctx = RCtx.from_code code in
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
            let _ = comp_type_check ctx comp rty in
            ())
      tasks
  in
  ()
