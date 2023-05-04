include Syntax

module StructureRaw = struct
  include StructureRaw

  let layout = To_expr.layout
  let layout_rty = To_rty.layout
  let layout_cty = To_rty.layout_cty
  let layout_regty = To_rty.layout_regty
  let layout_entry = To_structure.layout_entry
  let layout_structure = To_structure.layout
end

module Rty = struct
  include Rty

  let layout rty = RtyRaw.layout (To_typed_rty.to_opt_rty rty)
  let layout_cty rty = To_rty.layout_cty (To_typed_rty.to_opt_cty rty)
  let force_typed_rty = To_typed_rty.force_typed_rty
  let to_opt_rty = To_typed_rty.to_opt_rty

  open Sugar

  let layout_typed f { x; ty } = spf "%s: %s" (f x) (layout ty)

  let layout_typed_l f l =
    Zzdatatype.Datatype.List.split_by_comma (layout_typed f) l

  (* open P *)

  (* let ty_tr = Normalty.Ntyped.(Ty_constructor ("tr", [])) *)

  (* let mk_eq ty lit1 lit2 = *)
  (*   let f = "==" #: (construct_normal_tp ([ ty; ty ], bool_ty)) in *)
  (*   AApp (f, [ lit1; lit2 ]) *)

  (* let mk_select lit1 lit2 = *)
  (*   let f = "select" #: (construct_normal_tp ([ ty_tr; int_ty ], unit_ty)) in *)
  (*   AApp (f, [ lit1; lit2 ]) *)

  (* let mk_append h lit2 = *)
  (*   let f = "append" #: (construct_normal_tp ([ ty_tr; unit_ty ], ty_tr)) in *)
  (*   AApp (f, [ AVar h; lit2 ]) *)

  (* let mk_concat h1 h2 h = *)
  (*   let f = "concat" #: (construct_normal_tp ([ ty_tr; ty_tr ], ty_tr)) in *)
  (*   AApp (f, [ AVar h1; AVar h2; AVar h ]) *)

  (* let subst_cty_by_id id { v; phi } = P.subst_typed_id (v, id) phi *)
  (* let kw_h = "h" #: ty_tr *)
  (* let kw_h_prev = "h_prev" #: ty_tr *)
  (* let kw_v ty = "v" #: ty *)

  (* let mk_cty ty phif = *)
  (*   let v = kw_v ty in *)
  (*   { v; phi = phif v } *)

  (* let mk_octy ty phif = BaseRty { ou = Over; cty = mk_cty ty phif } *)
  (* let mk_otop ty = mk_octy ty (fun _ -> mk_true) *)
  (* let mk_ucty ty phif = BaseRty { ou = Under; cty = mk_cty ty phif } *)

  (* let mk_ucty_eq_lit_lit ty lit1 lit2 = *)
  (*   mk_ucty unit_ty (fun _ -> Lit (mk_eq ty lit1 lit2)) *)

  (* let mk_ucty_eq_lit ty lit = *)
  (*   mk_ucty ty (fun v -> Lit (mk_eq ty (AVar v) lit)) *)

  (* let mk_ucty_eq_c ty c = mk_ucty_eq_lit ty (P.AC c) *)
  (* let mk_ucty_eq_id ty id = mk_ucty_eq_lit ty P.(AVar id #: ty) *)
end

module Structure = struct
  include Structure

  let layout x = To_expr.layout @@ To_typed.to_opttyped_term x

  let layout_entry x =
    To_structure.layout_entry @@ To_typed.to_opttyped_struct_one x

  let layout_structure x = To_structure.layout @@ To_typed.to_opttyped_struct x
end

module RTypectx = struct
  include Typectx.F (Rty)
  include Rty

  let filter_map_rty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        | Mps _ | FuncImp _ | Func_dec _ | Type_dec _ -> None
        | Rty { name; kind; rty } -> f (name, kind, rty))
      code

  let from_code code =
    filter_map_rty
      (fun (name, kind, rty) ->
        let open Structure in
        match kind with RtyLib -> Some name #: rty | RtyToCheck -> None)
      code

  let get_task code =
    filter_map_rty
      (fun (name, kind, rty) ->
        let open Structure in
        match kind with RtyLib -> None | RtyToCheck -> Some (name, rty))
      code
end

module RTypedTermlang = struct
  include TypedTermlang

  let layout x = To_expr.layout @@ To_typed.to_opttyped_term x
end

module RTypedCoreEff = struct
  include Corelang.F (Rty)
end
