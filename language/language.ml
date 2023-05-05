include Syntax

module NTypectx = struct
  include Typectx.F (Nt)
  include Nt
end

module StructureRaw = struct
  include StructureRaw

  let layout_term = To_expr.layout
  let layout_rty = To_rty.layout
  let layout_cty = To_rty.layout_cty
  let layout_pty = To_rty.layout_pty
  let layout_regex = To_rty.layout_regex
  let layout_entry = To_structure.layout_entry
  let layout_structure = To_structure.layout
end

module Rty = struct
  open Coersion
  include Rty

  let layout_rty rty = StructureRaw.layout_rty (besome_rty rty)
  let layout_cty rty = StructureRaw.layout_cty (besome_cty rty)
  let layout_pty rty = StructureRaw.layout_pty (besome_pty rty)
  let layout_regex rty = StructureRaw.layout_regex (besome_regex rty)
  let layout = layout_rty

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
  open Coersion
  include Structure

  let layout_term x = StructureRaw.layout_term @@ besome_typed_term x
  let layout_entry x = StructureRaw.layout_entry @@ besome_entry x
  let layout_structure x = StructureRaw.layout_structure @@ besome_structure x
end

module RTypectx = struct
  include Typectx.F (Rty)
  include Rty

  let filter_map_rty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        | FuncImp _ | Func_dec _ | Type_dec _ -> None
        | Rty { name; kind; rty } -> f (name, kind, rty))
      code

  let from_code code =
    filter_map_rty
      (fun (name, kind, rty) ->
        let open Structure in
        match kind with RtyLib -> Some R.(name #: rty) | RtyToCheck -> None)
      code

  let get_task code =
    filter_map_rty
      (fun (name, kind, rty) ->
        let open Structure in
        match kind with RtyLib -> None | RtyToCheck -> Some (name, rty))
      code
end

(* module RTypedTermlang = struct *)
(*   include TypedTermlang *)

(*   let layout x = To_expr.layout @@ force_typed_term x *)
(* end *)

module RTypedCoreEff = struct
  include Corelang.F (Rty)
end
