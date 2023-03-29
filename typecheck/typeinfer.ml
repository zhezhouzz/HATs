open Language
module RCtx = RTypectx
module Nt = Normalty.Ntyped

(* module T = RTypedCoreEff *)
module R = Rty
module P = R.P
open TypedCoreEff

let ty_tr = Nt.Ty_constructor ("tr", [])
let kw_h = "h" #: ty_tr
let kw_v ty = "v" #: ty

let mk_basety ty phif =
  let v = kw_v ty in
  R.{ h = kw_h; v; phi = phif v }

let mk_obasety ty phif =
  let open R in
  BaseRty { ou = Over; basety = mk_basety ty phif }

let mk_ubasety ty phif =
  let open R in
  BaseRty { ou = Under; basety = mk_basety ty phif }

let mk_ubasety_eq_lit ty lit =
  let open P in
  mk_ubasety ty (fun v ->
      let eq = "==" #: (construct_normal_tp ([ ty; ty ], bool_ty)) in
      Lit (AApp (eq, [ AVar v; lit ])))

let mk_ubasety_eq_c ty c = mk_ubasety_eq_lit ty (P.AC c)
let mk_ubasety_eq_id ty id = mk_ubasety_eq_lit ty P.(AVar id #: ty)

open Sugar

let layout_comp = Denormalize.layout_comp
let layout_value = Denormalize.layout_value
let subtyping_check _ _ = ()

let unify_dep name rty =
  let open R in
  match rty with
  | BaseRty _ -> _failatwith __FILE__ __LINE__ ""
  | DepRty { dep; label; rarg; retrty } -> (
      match rarg.x with
      | Some x -> (dep, label, rarg, subst_id (x, name) retrty)
      | None -> (dep, label, rarg, retrty))

let rec value_type_infer (ctx : RCtx.ctx) (a : value typed) : R.t =
  let aty = a.ty in
  let rty =
    match a.x with
    | VConst c ->
        let rty = mk_ubasety_eq_c aty c in
        rty
    | VVar x ->
        let rty =
          match RCtx.get_ty_opt ctx x with
          | None -> _failatwith __FILE__ __LINE__ "cannot find rty"
          | Some _ -> mk_ubasety_eq_id aty x
        in
        rty
    | _ -> _failatwith __FILE__ __LINE__ ""
  in
  let () = RCtx.pretty_print_infer ctx (layout_value a, rty) in
  rty

and comp_type_infer (ctx : RCtx.ctx) (a : comp typed) : R.t =
  let aty = a.ty in
  let rty =
    match a.x with
    | CVal v -> value_type_infer ctx v #: aty
    | CApp { appf; apparg } ->
        let f_rty = value_type_infer ctx appf in
        let f_rty_argty = R.get_argty f_rty in
        (* let appargname, _ = (Rename.unique "a", apparg.ty) in *)
        let () = value_type_check ctx apparg f_rty_argty in
        (* let (_, _, _) = unify_dep appargname f_rty in *)
        (* let ctx' = RCtx.new_to_right ctx (R.( #: ) appargname f_rty_argty) in *)
        (* R.get_retty f_rty *)
        _failatwith __FILE__ __LINE__ ""
    | _ -> _failatwith __FILE__ __LINE__ ""
  in
  let () = RCtx.pretty_print_infer ctx (layout_comp a, rty) in
  rty

and value_type_check (ctx : RCtx.ctx) (a : value typed) (rty : R.t) : unit =
  let () = RCtx.pretty_print_judge ctx (layout_value a, rty) in
  let aty = a.ty in
  match a.x with
  | VConst _ | VVar _ -> subtyping_check (value_type_infer ctx a) rty
  | VFix { fixname; fixarg; fixbody } ->
      let self = R.( #: ) fixname.x rty in
      let ctx' = RCtx.new_to_right ctx self in
      let a' = (VLam { lamarg = fixarg; lambody = fixbody }) #: aty in
      value_type_check ctx' a' rty
  | VLam { lamarg; lambody } ->
      let dep, _, rarg, retrty = unify_dep lamarg.x rty in
      let () =
        match dep with R.Pi -> () | _ -> _failatwith __FILE__ __LINE__ "?"
      in
      let lamarg = R.( #: ) lamarg.x rarg.ty in
      let ctx' = RCtx.new_to_right ctx lamarg in
      comp_type_check ctx' lambody retrty
  | _ -> _failatwith __FILE__ __LINE__ ""

and comp_type_check (ctx : RCtx.ctx) (a : comp typed) (rty : R.t) : unit =
  let () = RCtx.pretty_print_judge ctx (layout_comp a, rty) in
  let aty = a.ty in
  match a.x with
  | CVal v -> value_type_check ctx v #: aty rty
  | CLetE { lhs; rhs; letbody } ->
      let rhs_rty = comp_type_infer ctx rhs in
      let ctx' = RCtx.new_to_right ctx (R.( #: ) lhs.x rhs_rty) in
      comp_type_check ctx' letbody rty
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
        | Some (_, comp) -> comp_type_check ctx comp rty)
      tasks
  in
  ()
