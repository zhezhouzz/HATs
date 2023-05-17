include Syntax

module NTypectx = struct
  include Nt
  include Typectx.FString (Nt)

  let new_to_right ctx Nt.{ x; ty } = new_to_right ctx (x, ty)

  let new_to_rights ctx l =
    let l = List.map (fun Nt.{ x; ty } -> (x, ty)) l in
    new_to_rights ctx l
end

module NOpTypectx = struct
  include Nt
  include Typectx.FOp (Nt)

  let to_builtin ctx : ctx = List.map (fun (x, ty) -> (Op.BuiltinOp x, ty)) ctx
end

module StructureRaw = struct
  include StructureRaw

  let layout_term = To_expr.layout
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
  let layout = layout_rty

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
end

module PCtxType = struct
  include Rty

  type t = pty
  type 'a typed = { x : 'a; ty : pty }

  (* open Sugar *)

  let ( #: ) x ty = { x; ty }
  let ( #-> ) f { x; ty } = { x = f x; ty }
  let layout = layout_pty
end

module RCtxType = struct
  include Rty

  type t = rty
  type 'a typed = { x : 'a; ty : rty }

  (* open Sugar *)

  let ( #: ) x ty = { x; ty }
  let ( #-> ) f { x; ty } = { x = f x; ty }
  let layout = layout_rty
  (* let layout_typed f { x; ty } = spf "%s:%s" (f x) (layout ty) *)

  (* let layout_typed_l f l = *)
  (*   Zzdatatype.Datatype.List.split_by_comma (layout_typed f) l *)
end

module Structure = struct
  open Coersion
  include Structure
  module R = RCtxType

  let layout_term x = StructureRaw.layout_term @@ besome_typed_term x
  let layout_entry x = StructureRaw.layout_entry @@ besome_entry x
  let layout_structure x = StructureRaw.layout_structure @@ besome_structure x
end

module POpTypectx = struct
  include PCtxType
  include Typectx.FOp (PCtxType)

  let to_nctx rctx =
    List.map (fun { x; ty } -> Nt.{ x; ty = erase_pty ty }) rctx
end

module PTypectx = struct
  include PCtxType
  include Typectx.FString (PCtxType)

  let new_to_right ctx PCtxType.{ x; ty } = new_to_right ctx (x, ty)

  let new_to_rights ctx l =
    let l = List.map (fun PCtxType.{ x; ty } -> (x, ty)) l in
    new_to_rights ctx l

  let filter_map_rty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        | EquationEntry _ | FuncImp _ | Func_dec _ | Type_dec _ -> None
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

  let to_opctx rctx = List.map (fun (x, ty) -> (Op.BuiltinOp x, ty)) rctx

  let op_and_rctx_from_code code =
    let opctx = NOpTypectx.from_kv_list @@ Structure.mk_normal_top_opctx code in
    let rctx = from_code code in
    let () = Pp.printf "@{<bold>R:@} %s\n" (layout_typed_l (fun x -> x) rctx) in
    let opctx, rctx =
      List.partition
        (fun (x, _) -> NOpTypectx.exists opctx (Op.BuiltinOp x))
        rctx
    in
    let opctx = to_opctx opctx in
    (* let () = *)
    (*   Pp.printf "@{<bold>Op:@} %s\n" *)
    (*     (ROpCtx.layout_typed_l Op.to_string typectx.opctx) *)
    (* in *)
    (opctx, rctx)
end

module RTypectx = struct
  include RCtxType
  include Typectx.FString (RCtxType)

  let new_to_right ctx RCtxType.{ x; ty } = new_to_right ctx (x, ty)

  let new_to_rights ctx l =
    let l = List.map (fun RCtxType.{ x; ty } -> (x, ty)) l in
    new_to_rights ctx l

  let filter_map_rty f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with
        | EquationEntry _ | FuncImp _ | Func_dec _ | Type_dec _ -> None
        | Rty { name; kind; rty } -> f (name, kind, rty))
      code

  (* let from_code code = *)
  (*   from_kv_list *)
  (*   @@ filter_map_rty *)
  (*        (fun (name, kind, rty) -> *)
  (*          let open Structure in *)
  (*          match kind with RtyLib -> Some (name, rty) | RtyToCheck -> None) *)
  (*        code *)

  let get_task code =
    filter_map_rty
      (fun (name, kind, rty) ->
        let open Structure in
        match kind with RtyLib -> None | RtyToCheck -> Some (name, rty))
      code

  (* let op_and_rctx_from_code code = *)
  (*   let opctx = NOpTypectx.from_kv_list @@ Structure.mk_normal_top_opctx code in *)
  (*   let rctx = from_code code in *)
  (*   let () = Pp.printf "@{<bold>R:@} %s\n" (layout_typed_l (fun x -> x) rctx) in *)
  (*   let opctx, rctx = *)
  (*     List.partition *)
  (*       (fun { x; _ } -> NOpTypectx.exists opctx (Op.BuiltinOp x)) *)
  (*       rctx *)
  (*   in *)
  (*   let opctx = *)
  (*     List.map *)
  (*       (fun { x; ty } -> *)
  (*         POpTypectx.{ x = Op.BuiltinOp x; ty = rty_force_pty ty }) *)
  (*       opctx *)
  (*   in *)
  (*   (\* let () = *\) *)
  (*   (\*   Pp.printf "@{<bold>Op:@} %s\n" *\) *)
  (*   (\*     (ROpCtx.layout_typed_l Op.to_string typectx.opctx) *\) *)
  (*   (\* in *\) *)
  (*   (opctx, rctx) *)
end

(* module RTypedTermlang = struct *)
(*   include TypedTermlang *)

(*   let layout x = To_expr.layout @@ force_typed_term x *)
(* end *)

module TypedCoreEff = struct
  include Corelang.F (Nt)
  open Sugar

  let _value_to_lit file line v =
    match v.x with
    | VVar name -> Rty.P.AVar name
    | VConst c -> Rty.P.AC c
    | VLam _ -> _failatwith file line "?"
    | VFix _ -> _failatwith file line "?"
    | VTu _ -> _failatwith file line "?"
end

module Eqctx = struct
  include Equation

  type ctx = equation list

  open Zzdatatype.Datatype
  open Sugar

  let layout_ret_res = function
    | RetResLit lit -> spf "ret_res %s" (Rty.layout_lit lit)
    | Drop -> "Drop"

  let layout_equation e =
    To_algebraic.layout_equation @@ Coersion.besome_equation e

  let layout_equations e = List.split_by " ; " layout_equation e

  let find_ret_rules ctx (op1, args1) (op2, args2) =
    let () =
      Printf.printf "find_ret_rules: <%s(%s)><%s(%s)>\n" op1
        (List.split_by_comma Rty.layout_lit args1)
        op2
        (List.split_by_comma Rty.layout_lit args2)
    in
    match_equation_2op ctx (op1, args1) (op2, args2)

  let find_none_ret_rules ctx (op2, args2) =
    let () =
      Printf.printf "find_none_ret_rules: <%s(%s)>\n" op2
        (List.split_by_comma Rty.layout_lit args2)
    in
    let () = Printf.printf "%s\n" @@ layout_equations ctx in
    match_equation_1op ctx (op2, args2)

  let filter_map_equation f code =
    List.filter_map
      (fun code ->
        let open Structure in
        match code with EquationEntry e -> f e | _ -> None)
      code

  let from_code code = filter_map_equation (fun e -> Some e) code
  (* let from_code code = *)
  (* filter_map_rty *)
  (*   (fun (name, kind, rty) -> *)
  (*     let open Structure in *)
  (*     match kind with RtyLib -> Some R.(name #: rty) | RtyToCheck -> None) *)
  (*   code *)
end
