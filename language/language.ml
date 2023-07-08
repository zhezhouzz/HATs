include Syntax

module NTypectx = struct
  include Nt
  include Typectx.FString

  type ctx = Nt.t poly_ctx

  let new_to_right ctx { x; ty } = new_to_right ctx (x, ty)

  let new_to_rights ctx l =
    let l = List.map (fun { x; ty } -> (x, ty)) l in
    new_to_rights ctx l

  let _f = layout
  let layout_typed = layout_typed _f
  let layout_typed_l = layout_typed_l _f
  let pretty_print = pretty_print _f
  let pretty_print_lines = pretty_print_lines _f
  let pretty_print_infer = pretty_print_infer _f
  let pretty_print_judge = pretty_print_judge _f
  let pretty_layout = pretty_layout _f
end

module NOpTypectx = struct
  include Nt
  include Typectx.FOp

  type ctx = Nt.t poly_ctx

  let to_builtin ctx : ctx = List.map (fun (x, ty) -> (Op.BuiltinOp x, ty)) ctx
  let new_to_right ctx { x; ty } = new_to_right ctx (x, ty)
  let _f = layout
  let layout_typed = layout_typed _f
  let layout_typed_l = layout_typed_l _f
  let pretty_print = pretty_print _f
  let pretty_print_lines = pretty_print_lines _f
  let pretty_print_infer = pretty_print_infer _f
  let pretty_print_judge = pretty_print_judge _f
  let pretty_layout = pretty_layout _f
end

module StructureRaw = struct
  include StructureRaw

  let layout_term = To_expr.layout
  let layout_term_omit_type = To_expr.layout_omit_type
  let layout_rty = To_rty.layout
  let layout_cty = To_rty.layout_cty
  let layout_pty = To_rty.layout_pty
  let layout_regex = To_rty.layout_regex
  let layout_sevent = To_rty.layout_sevent
  let layout_entry = To_structure.layout_entry
  let layout_structure = To_structure.layout
end

module Rty = struct
  open Coersion
  include Rty

  let layout_lit lit = To_lit.layout_lit (besome_lit lit)
  let layout_prop prop = To_qualifier.layout (besome_qualifier prop)
  let layout_rty rty = StructureRaw.layout_rty (besome_rty rty)
  let layout_cty rty = StructureRaw.layout_cty (besome_cty rty)
  let layout_pty rty = StructureRaw.layout_pty (besome_pty rty)
  let layout_regex rty = StructureRaw.layout_regex (besome_regex rty)
  let layout_sevent rty = StructureRaw.layout_sevent (besome_sevent rty)

  open Sugar

  (* let layout_typed f { x; ty } = spf "%s: %s" (f x) (layout ty) *)

  (* let layout_typed_l f l = *)
  (*   Zzdatatype.Datatype.List.split_by_comma (layout_typed f) l *)

  let mk_lit_var_eq_lit v c =
    let open L in
    let eqsym =
      (Op.BuiltinOp "==") #: (construct_arr_tp ([ v.ty; v.ty ], bool_ty))
    in
    AAppOp (eqsym, [ (AVar v.x) #: v.ty; c #: v.ty ])

  let mk_prop_var_eq_lit v c =
    let open L in
    match c with
    | AC Const.U -> mk_true
    | AC (Const.B b) -> if b then Lit (AVar v.x) else Not (Lit (AVar v.x))
    | _ -> P.Lit (mk_lit_var_eq_lit v c)

  let mk_cty_var_eq_lit ty c =
    let v = Nt.{ x = v_name; ty } in
    { v; phi = mk_prop_var_eq_lit v c }

  let mk_pty_var_eq_lit ty c = BasePty { cty = mk_cty_var_eq_lit ty c }
  let mk_pty_var_eq_c ty c = mk_pty_var_eq_lit ty L.(AC c)
  let mk_pty_var_eq_var var = mk_pty_var_eq_lit var.L.ty L.(AVar var.L.x)

  let find_lit_assignment_from_prop prop x =
    match x.Nt.ty with
    | Nt.Ty_bool -> find_boollit_assignment_from_prop prop x.Nt.x
    | Nt.Ty_int -> find_intlit_assignment_from_prop prop x.Nt.x
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let mk_effevent_eq_args args =
    let vs = vs_names (List.length args) in
    let vs, props =
      List.split
      @@ List.map (fun (v, lit) ->
             let v = Nt.(v #: lit.ty) in
             (v, mk_prop_var_eq_lit v lit.x))
      @@ _safe_combine __FILE__ __LINE__ vs args
    in
    (vs, props)

  (* here we need to garantee that the free variable in xphi is indeed v *)
  let mk_effevent_from_application_with_cty (op, args) (cty : cty) =
    let () =
      _assert __FILE__ __LINE__ "the cty should be normalized with fv v"
        (String.equal v_name cty.v.x)
    in
    let vs, props = mk_effevent_eq_args args in
    let phix = subst_prop_id (cty.v.x, v_ret_name) cty.phi in
    let v = Nt.{ x = v_ret_name; ty = cty.v.ty } in
    EffEvent { op; vs; v; phi = smart_and (phix :: props) }

  let mk_effevent_from_application_with_var (op, args) (x : string Nt.typed) =
    let vs, props = mk_effevent_eq_args args in
    let v = Nt.{ x = v_ret_name; ty = x.ty } in
    let phix =
      if Nt.(eq unit_ty v.ty) then mk_true else mk_prop_var_eq_lit v (AVar x.x)
    in
    EffEvent { op; vs; v; phi = smart_and (phix :: props) }
end

module Structure = struct
  open Coersion
  include Structure
  module R = Rty

  let layout_term x = StructureRaw.layout_term @@ besome_typed_term x

  let layout_term_omit_type x =
    StructureRaw.layout_term_omit_type @@ besome_typed_term x

  let layout_entry x = StructureRaw.layout_entry @@ besome_entry x
  let layout_structure x = StructureRaw.layout_structure @@ besome_structure x
end

module POpTypectx = struct
  include Rty
  include Typectx.FOp
  open Sugar

  type ctx = pty list poly_ctx

  open Zzdatatype.Datatype

  let _f = List.split_by_comma layout_pty
  let layout_typed = layout_typed _f
  let layout_typed_l = layout_typed_l _f
  let pretty_print = pretty_print _f
  let pretty_print_lines = pretty_print_lines _f
  let pretty_print_infer = pretty_print_infer _f
  let pretty_print_judge = pretty_print_judge _f
  let pretty_layout = pretty_layout _f

  let filter_map_rty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        (* | EquationEntry _ *)
        | FuncImp _ | Func_dec _ | Type_dec _ -> None
        | Rty { name; kind; rty } -> f (name, kind, rty_force_pty rty))
      code

  let to_opctx rctx = List.map (fun (x, ty) -> (Op.BuiltinOp x, [ ty ])) rctx

  let to_opctx_if_cap rctx =
    let cond x = String.equal x (String.capitalize_ascii x) in
    let effpctx =
      List.filter_map
        (fun (x, ty) -> if cond x then Some (x, ty) else None)
        rctx
    in
    let pctx = List.filter (fun (x, _) -> not (cond x)) rctx in
    (effpctx, pctx)

  let to_effopctx l =
    let tab = Hashtbl.create 10 in
    let () =
      List.iter
        (fun (name, pty) ->
          match Hashtbl.find_opt tab name with
          | None -> Hashtbl.add tab name [ pty ]
          | Some ptys -> Hashtbl.replace tab name (pty :: ptys))
        l
    in
    let l = List.of_seq @@ Hashtbl.to_seq tab in
    let l = List.map (fun (x, ty) -> (Op.EffOp x, ty)) l in
    l

  let to_pureopctx l = List.map (fun (x, ty) -> (Op.BuiltinOp x, [ ty ])) l

  let from_code code =
    let opctx = NOpTypectx.from_kv_list @@ Structure.mk_normal_top_opctx code in
    (* let () = Pp.printf "@{<bold>R:@} %s\n" (NOpTypectx.layout_typed_l opctx) in *)
    (* let () = failwith "end" in *)
    let l =
      from_kv_list
      @@ filter_map_rty
           (fun (name, kind, rty) ->
             let open Structure in
             match kind with RtyLib -> Some (name, rty) | RtyToCheck -> None)
           code
    in
    let pure_opctx, rctx =
      List.partition (fun (x, _) -> NOpTypectx.exists opctx (Op.BuiltinOp x)) l
    in
    let pure_opctx = to_pureopctx pure_opctx in
    let eff_opctx, rctx = to_opctx_if_cap rctx in
    let eff_opctx = to_effopctx eff_opctx in
    let opctx = pure_opctx @ eff_opctx in
    (opctx, rctx)

  (* let op_and_rctx_from_code code = *)
  (*   let effctx, rctx = from_code code in *)
  (*   let () = Pp.printf "@{<bold>R:@} %s\n" (layout_typed_l rctx) in *)
  (*   let opctx, rctx = *)
  (*     List.partition *)
  (*       (fun (x, _) -> NOpTypectx.exists opctx (Op.BuiltinOp x)) *)
  (*       rctx *)
  (*   in *)
  (*   let opctx = effctx @ to_opctx opctx in *)
  (*   (\* let () = *\) *)
  (*   (\*   Pp.printf "@{<bold>Op:@} %s\n" *\) *)
  (*   (\*     (ROpCtx.layout_typed_l Op.to_string typectx.opctx) *\) *)
  (*   (\* in *\) *)
  (*   (opctx, rctx) *)

  let to_nctx rctx =
    List.map
      (fun (x, ty) ->
        match ty with
        | ty :: _ -> (x, erase_pty ty)
        | _ -> _failatwith __FILE__ __LINE__ "die")
      rctx
end

module PTypectx = struct
  include Rty
  include Typectx.FString

  type ctx = pty poly_ctx

  let new_to_right ctx { px; pty } = new_to_right ctx (px, pty)

  let new_to_rights ctx l =
    let l = List.map (fun { px; pty } -> (px, pty)) l in
    new_to_rights ctx l

  let _f = layout_pty
  let layout_typed = layout_typed _f
  let layout_typed_l = layout_typed_l _f
  let pretty_print = pretty_print _f
  let pretty_print_lines = pretty_print_lines _f
  let pretty_print_infer = pretty_print_infer _f
  let pretty_print_judge = pretty_print_judge _f

  let filter_map_rty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        (* | EquationEntry _ *)
        | FuncImp _ | Func_dec _ | Type_dec _ -> None
        | Rty { name; kind; rty } -> f (name, kind, rty_force_pty rty))
      code

  let from_code code =
    from_kv_list
    @@ filter_map_rty
         (fun (name, kind, rty) ->
           let open Structure in
           match kind with RtyLib -> Some (name, rty) | RtyToCheck -> None)
         code

  (* let get_task code = *)
  (*   filter_map_rty *)
  (*     (fun (name, kind, rty) -> *)
  (*       let open Structure in *)
  (*       match kind with RtyLib -> None | RtyToCheck -> Some (name, rty)) *)
  (*     code *)
end

module RTypectx = struct
  include Rty
  include Typectx.FString

  type ctx = rty poly_ctx

  let new_to_right ctx { rx; rty } = new_to_right ctx (rx, rty)

  let new_to_rights ctx l =
    let l = List.map (fun { rx; rty } -> (rx, rty)) l in
    new_to_rights ctx l

  let _f = layout_rty
  let layout_typed = layout_typed _f
  let layout_typed_l = layout_typed_l _f
  let pretty_print = pretty_print _f
  let pretty_print_lines = pretty_print_lines _f
  let pretty_print_infer = pretty_print_infer _f
  let pretty_print_judge = pretty_print_judge _f

  let filter_map_rty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        (* | EquationEntry _ *)
        | FuncImp _ | Func_dec _ | Type_dec _ -> None
        | Rty { name; kind; rty } -> f (name, kind, rty))
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

module TypedCoreEff = struct
  include Corelang.F (Nt)
  open Sugar

  let _value_to_lit file line v =
    let lit =
      match v.x with
      | VVar name -> Rty.P.AVar name
      | VConst c -> Rty.P.AC c
      | VLam _ -> _failatwith file line "?"
      | VFix _ -> _failatwith file line "?"
      | VTu _ -> _failatwith file line "?"
    in
    lit #: v.ty
end
