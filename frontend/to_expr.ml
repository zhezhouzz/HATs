module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
open Syntax
open StructureRaw

let kw_perform = "perform"
let kw_builtin = "pmop"

let get_if_rec flag =
  match flag with Asttypes.Recursive -> true | Asttypes.Nonrecursive -> false

let mk_idloc names =
  match Longident.unflatten names with
  | None -> failwith "die"
  | Some id -> Location.mknoloc id

let desc_to_ocamlexpr desc =
  {
    pexp_desc = desc;
    pexp_loc = Location.none;
    pexp_loc_stack = [];
    pexp_attributes = [];
  }

let typed_to_ocamlexpr_desc f expr =
  match expr.ty with
  | None -> f expr.x
  | Some ty ->
      Pexp_constraint (desc_to_ocamlexpr @@ f expr.x, Type.t_to_core_type ty)

let expr_to_untyped_expr expr =
  let rec aux expr =
    let res =
      match expr.x with
      | Err -> Err
      | Tu es -> Tu (List.map aux es)
      | Var var -> Var var
      | Const c -> Const c
      | Let { if_rec; lhs; rhs; letbody } ->
          Let { if_rec; lhs; rhs = aux rhs; letbody = aux letbody }
      | AppOp (op, args) -> AppOp (op, List.map aux args)
      | App (func, args) -> App (aux func, List.map aux args)
      | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
      | Match (case_target, cs) ->
          let cs =
            List.map
              (fun { constructor; args; exp } ->
                { constructor; args; exp = aux exp })
              cs
          in
          Match (aux case_target, cs)
      | Lam { lamarg; lambody } -> Lam { lamarg; lambody = aux lambody }
    in
    res #: None
  in
  aux expr

let rec expr_to_ocamlexpr expr =
  desc_to_ocamlexpr @@ typed_expr_to_ocamlexpr_desc expr

and typed_expr_to_ocamlexpr_desc expr =
  typed_to_ocamlexpr_desc expr_to_ocamlexpr_desc expr

and typed_id_to_ocamlexpr id = expr_to_ocamlexpr { ty = id.ty; x = Var id.x }

and typed_op_to_ocamlexpr op =
  typed_id_to_ocamlexpr @@ (To_op.op_to_string #-> op)

and expr_to_ocamlexpr_desc expr =
  let aux expr =
    match expr with
    | Err -> Pexp_ident (mk_idloc [ "Err" ])
    | Tu es -> Pexp_tuple (List.map expr_to_ocamlexpr es)
    | Var var ->
        (* let () = Printf.printf "print var: %s\n" var in *)
        Pexp_ident (mk_idloc [ var ])
    | Const v -> (To_const.value_to_expr v).pexp_desc
    | Let { if_rec; lhs; rhs; letbody } ->
        let flag =
          if if_rec then Asttypes.Recursive else Asttypes.Nonrecursive
        in
        let vb =
          {
            pvb_pat = To_pat.typed_ids_to_pattern lhs;
            pvb_expr = expr_to_ocamlexpr rhs;
            pvb_attributes = [];
            pvb_loc = Location.none;
          }
        in
        Pexp_let (flag, [ vb ], expr_to_ocamlexpr letbody)
    | AppOp (op, args) ->
        let mk_app f args =
          match op.x with
          | Op.BuiltinOp _ ->
              let kw = typed_id_to_ocamlexpr kw_builtin #: None in
              Pexp_apply (kw, (Asttypes.Nolabel, f) :: args)
          | Op.DtOp _ -> Pexp_apply (f, args)
          | Op.EffOp _ ->
              let kw = typed_id_to_ocamlexpr kw_perform #: None in
              Pexp_apply (kw, (Asttypes.Nolabel, f) :: args)
        in
        let op = typed_op_to_ocamlexpr op in
        let args =
          List.map (fun x -> (Asttypes.Nolabel, expr_to_ocamlexpr x)) args
        in
        mk_app op args
    | App (func, args) ->
        let func = expr_to_ocamlexpr func in
        let args =
          List.map (fun x -> (Asttypes.Nolabel, expr_to_ocamlexpr x)) args
        in
        Pexp_apply (func, args)
    | Ite (e1, e2, e3) ->
        let e1, e2, e3 = Sugar.map3 expr_to_ocamlexpr (e1, e2, e3) in
        Pexp_ifthenelse (e1, e2, Some e3)
    | Match (case_target, cs) ->
        let case_target = expr_to_ocamlexpr case_target in
        let cases = List.map match_case_aux cs in
        Pexp_match (case_target, cases)
    | Lam { lamarg; lambody } ->
        Pexp_fun
          ( Asttypes.Nolabel,
            None,
            To_pat.typed_ids_to_pattern [ lamarg ],
            expr_to_ocamlexpr lambody )
  in
  aux expr

and match_case_aux { constructor; args; exp } =
  let args = List.map (fun x -> (fun x -> Var x) #-> x) args in
  let lhs =
    To_pat.term_to_pattern
      (AppOp ((fun x -> Op.DtOp x) #-> constructor, args)) #: None
  in
  { pc_lhs = lhs; pc_guard = None; pc_rhs = expr_to_ocamlexpr exp }

let id_to_ocamlexpr id = typed_id_to_ocamlexpr id #: None

open Sugar

let id_to_var id = (fun x -> Var x) #-> id

let update_ty { x; ty } ty' =
  match ty with None -> x #: (Some ty') | Some _ -> x #: (Some ty')

let expr_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_tuple es -> (Tu (List.map aux es)) #: None
    | Pexp_constraint (expr, ty) ->
        (* let _ = Printf.printf "ct: %s\n" (Type.layout_ ty) in *)
        let ty = Type.core_type_to_t ty in
        let res = update_ty (aux expr) ty in
        res
    | Pexp_ident id -> id_to_var @@ ((To_id.longid_to_id id) #: None)
    | Pexp_construct (c, args) -> (
        (* let () = *)
        (*   Printf.printf "check op: %s\n" (Pprintast.string_of_expression expr) *)
        (* in *)
        let c = To_pat.constructor_to_term_or_op @@ To_id.longid_to_id c in
        (* let () = Printf.printf "Pat: %s\n" c in *)
        match c with
        | To_pat.C_is_term tm -> tm
        | To_pat.C_is_op op -> (
            match args with
            | None -> (AppOp (op, [])) #: None
            | Some args -> (
                let args = aux args in
                match args.x with
                | Tu es -> (AppOp (op, es)) #: None
                | _ -> (AppOp (op, [ args ])) #: None)))
    | Pexp_constant _ -> (Const (To_const.expr_to_value expr)) #: None
    | Pexp_let (flag, vbs, e) ->
        List.fold_right
          (fun vb letbody ->
            (Let
               {
                 if_rec = get_if_rec flag;
                 lhs = To_pat.patten_to_typed_ids vb.pvb_pat;
                 rhs = aux vb.pvb_expr;
                 letbody;
               })
            #: None)
          vbs (aux e)
    | Pexp_apply (func, args) -> (
        let func = aux func in
        match func.x with
        | Var name when String.equal name kw_perform -> (
            match args with
            | [ (_, arg) ] -> (
                let res = aux arg in
                match res.x with
                | AppOp (_, _) -> res
                | _ -> _failatwith __FILE__ __LINE__ "Syntax Error: perform")
            | _ -> _failatwith __FILE__ __LINE__ "Syntax Error: perform")
        | Var name when String.equal name kw_builtin -> (
            match args with
            | [ (_, arg) ] -> (
                let res = aux arg in
                match res.x with
                | App ({ x = Var op; ty }, args) ->
                    (AppOp ({ x = Op.BuiltinOp op; ty }, args)) #: res.ty
                | _ -> _failatwith __FILE__ __LINE__ "Syntax Error: builtin")
            | _ -> _failatwith __FILE__ __LINE__ "Syntax Error: builtin")
        | _ -> (App (func, List.map (fun x -> aux @@ snd x) args)) #: None)
    | Pexp_ifthenelse (e1, e2, Some e3) ->
        (Ite (aux e1, aux e2, aux e3)) #: None
    | Pexp_ifthenelse (_, _, None) -> raise @@ failwith "no else branch in ite"
    | Pexp_match (case_target, cases) ->
        let cs =
          List.map
            (fun case ->
              match (To_pat.pattern_to_term case.pc_lhs).x with
              | AppOp ({ x = Op.DtOp op; ty }, args) ->
                  {
                    constructor = { x = op; ty };
                    args = List.map to_var args;
                    exp = aux case.pc_rhs;
                  }
              | _ -> _failatwith __FILE__ __LINE__ "?")
            cases
        in
        (Match (aux case_target, cs)) #: None
    | Pexp_fun (_, _, arg0, expr) ->
        let arg = To_pat.pattern_to_term arg0 in
        let () =
          match arg.ty with
          | None ->
              failwith "Syntax error: lambda function should provide types"
          | Some _ -> ()
        in
        let lamarg =
          match arg.x with
          | Var x -> x #: arg.ty
          | _ ->
              let () = Printf.printf "%s\n" (To_pat.layout_ arg0) in
              failwith "Syntax error: lambda function wrong argument"
        in
        (Lam { lamarg; lambody = aux expr }) #: None
        (* un-curry *)
    | _ ->
        raise
        @@ failwith
             (Sugar.spf "not imp client parsing:%s"
             @@ Pprintast.string_of_expression expr)
  in
  aux expr

let typed_id_of_ocamlexpr expr =
  let x = expr_of_ocamlexpr expr in
  match x.x with Var id -> id #: x.ty | _ -> _failatwith __FILE__ __LINE__ "?"

let id_of_ocamlexpr expr = (typed_id_of_ocamlexpr expr).x
let layout x = Pprintast.string_of_expression @@ expr_to_ocamlexpr x
let layout_omit_type x = layout @@ expr_to_untyped_expr x

(* let prim_dt = [ "[]"; "::" ] *)
(* let is_prim_dt x = List.exists (String.equal x) prim_dt *)

(* let op_of_string_opt x = try Some (op_of_string x) with _ -> None *)
