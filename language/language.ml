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
  let layout_lit = To_lit.layout
  let layout_prop = To_qualifier.layout
  let layout_sevent = To_se.layout
  let layout_regex = To_srl.layout
  let layout_ltlf = To_ltlf.layout
  let layout_cty = To_cty.layout
  let layout_hty = To_rty.layout_hty
  let layout_rty = To_rty.layout_rty
  let layout_ltlf_hty = To_ltlf_hty.layout_hty
  let layout_ltlf_rty = To_ltlf_hty.layout_rty
  let layout_entry = To_structure.layout_entry
  let layout_structure = To_structure.layout
end

module Rty = struct
  include Rty

  let layout_lit lit = To_lit.layout (Coersion.Lit.besome lit)
  let layout_prop prop = To_qualifier.layout (Coersion.Qualifier.besome prop)
  let layout_sevent se = To_se.layout (Coersion.Se.besome se)
  let layout_regex se = To_srl.layout (Coersion.SRL.besome se)
  let layout_ltlf se = To_ltlf.layout (Coersion.LTLf.besome se)
  let layout_cty se = To_cty.layout (Coersion.Cty.besome se)
  let layout_rty se = To_rty.layout_rty (Coersion.Rty.besome_rty se)
  let layout_hty se = To_rty.layout_hty (Coersion.Rty.besome_hty se)
  (* let layout_hty = To_ltlf_hty.layout_hty *)
  (* let layout_rty = To_ltlf_hty.layout_rty *)
  (* let layout_entry = To_structure.layout_entry *)
  (* let layout_structure = To_structure.layout *)
  (* let layout_hty hty = StructureRaw.layout_hty (besome_hty hty) *)
  (* let layout_cty hty = StructureRaw.layout_cty (besome_cty hty) *)
  (* let layout_rty hty = StructureRaw.layout_rty (besome_rty hty) *)
  (* let layout_regex hty = StructureRaw.layout_regex (besome_regex hty) *)
  (* let layout_sevent hty = StructureRaw.layout_sevent (besome_sevent hty) *)

  open Sugar
  open Common

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

  let mk_rty_var_eq_lit ty c = BaseRty { cty = mk_cty_var_eq_lit ty c }
  let mk_rty_var_eq_c ty c = mk_rty_var_eq_lit ty L.(AC c)
  let mk_rty_var_eq_var var = mk_rty_var_eq_lit var.L.ty L.(AVar var.L.x)

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

  (* gather lits/rtys *)

  open Zzdatatype.Datatype

  type gathered_lits = {
    global_lits : lit list;
    local_lits : (string Nt.typed list * lit list) StrMap.t;
  }

  let gathered_lits_init () = { global_lits = []; local_lits = StrMap.empty }

  let gathered_rm_dup { global_lits; local_lits } =
    let global_lits = List.slow_rm_dup eq_lit global_lits in
    let local_lits =
      StrMap.map
        (fun (vs, lits) -> (vs, List.slow_rm_dup eq_lit lits))
        local_lits
    in
    { global_lits; local_lits }

  let gather_from_sevent { global_lits; local_lits } sevent =
    match sevent with
    | GuardEvent phi ->
        { global_lits = P.get_lits phi @ global_lits; local_lits }
    | EffEvent { op; phi; vs; v } ->
        let lits = P.get_lits phi in
        let vs' = List.map (fun x -> x.Nt.x) (v :: vs) in
        let is_contain_local_free lit =
          match List.interset ( == ) vs' @@ P.fv_lit lit with
          | [] -> false
          | _ -> true
        in
        let llits, glits = List.partition is_contain_local_free lits in
        let local_lits =
          StrMap.update op
            (fun l ->
              match l with
              | None -> Some (v :: vs, llits)
              | Some (_, l) -> Some (v :: vs, l @ llits))
            local_lits
        in
        let global_lits = global_lits @ glits in
        { global_lits; local_lits }

  let gather_from_regex regex =
    let rec aux regex m =
      match regex with
      | EmptyA -> m
      | AnyA -> m
      | EpsilonA -> m
      | EventA se -> gather_from_sevent m se
      | LorA (t1, t2) -> aux t1 @@ aux t2 m
      | SetMinusA (t1, t2) -> aux t1 @@ aux t2 m
      | LandA (t1, t2) -> aux t1 @@ aux t2 m
      | SeqA (t1, t2) -> aux t1 @@ aux t2 m
      | StarA t -> aux t m
      | ComplementA t -> aux t m
    in
    aux regex (gathered_lits_init ())
end

module Structure = struct
  include Structure
  module R = Rty

  let layout_term x =
    StructureRaw.layout_term @@ Coersion.TermLang.besome_typed_term x

  let layout_term_omit_type x =
    StructureRaw.layout_term_omit_type @@ Coersion.TermLang.besome_typed_term x

  let layout_entry x =
    StructureRaw.layout_entry @@ Coersion.Structure.besome_entry x

  let layout_structure x =
    StructureRaw.layout_structure @@ Coersion.Structure.besome_structure x
end

module ROpTypectx = struct
  include Rty
  include Typectx.FOp
  open Sugar

  type ctx = rty poly_ctx

  open Zzdatatype.Datatype

  let _f = List.split_by_comma layout_rty
  let layout_typed = layout_typed _f
  let layout_typed_l = layout_typed_l _f
  let pretty_print = pretty_print _f
  let pretty_print_lines = pretty_print_lines _f
  let pretty_print_infer = pretty_print_infer _f
  let pretty_print_judge = pretty_print_judge _f
  let pretty_layout = pretty_layout _f

  let filter_map_hty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        (* | EquationEntry _ *)
        | FuncImp _ | Func_dec _ | Type_dec _ -> None
        | Rty { name; kind; rty } -> f (name, kind, rty)
        | LtlfRty _ -> None)
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
        (fun (name, rty) ->
          match Hashtbl.find_opt tab name with
          | None -> Hashtbl.add tab name [ rty ]
          | Some rtys -> Hashtbl.replace tab name (rty :: rtys))
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
      @@ filter_map_hty
           (fun (name, kind, hty) ->
             let open Structure in
             match kind with RtyLib -> Some (name, hty) | RtyToCheck -> None)
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
        | ty :: _ -> (x, erase_rty ty)
        | _ -> _failatwith __FILE__ __LINE__ "die")
      rctx
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

  let filter_map_hty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        (* | EquationEntry _ *)
        | FuncImp _ | Func_dec _ | Type_dec _ -> None
        | Rty { name; kind; rty } -> f (name, kind, rty)
        | LtlfRty _ -> None)
      code

  (* let get_rtys_from_code code = filter_map_hty (fun x -> x) code *)

  let from_code code =
    from_kv_list
    @@ filter_map_hty
         (fun (name, kind, hty) ->
           let open Structure in
           match kind with RtyLib -> Some (name, hty) | RtyToCheck -> None)
         code

  let get_task code =
    filter_map_hty
      (fun (name, kind, hty) ->
        let open Structure in
        match kind with RtyLib -> None | RtyToCheck -> Some (name, hty))
      code
end

(* module RTypectx = struct *)
(*   include Rty *)
(*   include Typectx.FString *)

(*   type ctx = hty poly_ctx *)

(*   let new_to_right ctx { rx; hty } = new_to_right ctx (rx, hty) *)

(*   let new_to_rights ctx l = *)
(*     let l = List.map (fun { rx; hty } -> (rx, hty)) l in *)
(*     new_to_rights ctx l *)

(*   let _f = layout_hty *)
(*   let layout_typed = layout_typed _f *)
(*   let layout_typed_l = layout_typed_l _f *)
(*   let pretty_print = pretty_print _f *)
(*   let pretty_print_lines = pretty_print_lines _f *)
(*   let pretty_print_infer = pretty_print_infer _f *)
(*   let pretty_print_judge = pretty_print_judge _f *)

(*   let filter_map_hty f code = *)
(*     List.filter_map *)
(*       (fun code -> *)
(*         let open Structure in *)
(*         match code with *)
(*         (\* | EquationEntry _ *\) *)
(*         | FuncImp _ | Func_dec _ | Type_dec _ -> None *)
(*         | Rty { name; kind; hty } -> f (name, kind, hty)) *)
(*       code *)

(*   let get_task code = *)
(*     filter_map_hty *)
(*       (fun (name, kind, hty) -> *)
(*         let open Structure in *)
(*         match kind with RtyLib -> None | RtyToCheck -> Some (name, hty)) *)
(*       code *)
(* end *)

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
