module MetaEnv = Env
open Ocaml_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Op = Ast.Pmop
open Ast.OptTypedTermlang

let kw_perform = "perform"
let kw_match_with = "match_with"
let kw_retc = "Retc"

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

let rec expr_to_ocamlexpr expr =
  desc_to_ocamlexpr @@ typed_expr_to_ocamlexpr_desc expr

and typed_expr_to_ocamlexpr_desc expr =
  match expr.ty with
  | None -> expr_to_ocamlexpr_desc expr.x
  | Some ty ->
      Pexp_constraint
        ( desc_to_ocamlexpr @@ expr_to_ocamlexpr_desc expr.x,
          Type.t_to_core_type ty )

and id_to_ocamlexpr id = expr_to_ocamlexpr { ty = id.ty; x = Var id.x }

and expr_to_ocamlexpr_desc expr =
  let aux expr =
    match expr with
    | Err -> Pexp_ident (mk_idloc [ "Err" ])
    | Tu es -> Pexp_tuple (List.map expr_to_ocamlexpr es)
    | Var var ->
        (* let () = Printf.printf "print var: %s\n" var in *)
        Pexp_ident (mk_idloc [ var ])
    | Const v -> (To_const.value_to_expr v).pexp_desc
    | VHd hd -> hd_aux hd.x
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
        let func = id_to_ocamlexpr @@ xmap Op.t_to_string op in
        let args =
          List.map (fun x -> (Asttypes.Nolabel, expr_to_ocamlexpr x)) args
        in
        Pexp_apply (func, args)
    | Perform { rhsop; rhsargs } ->
        let op = xmap (fun x -> Op.DtConstructor x) rhsop in
        let perform = (Var kw_perform) #: None in
        expr_to_ocamlexpr_desc
          (App (perform, [ (AppOp (op, rhsargs)) #: None ]))
    | CWithH { handler; handled_prog } ->
        let match_with = (Var kw_match_with) #: None in
        expr_to_ocamlexpr_desc
          (App (match_with, [ handled_prog; (VHd handler) #: handler.ty ]))
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
        let cases =
          List.map
            (fun case ->
              let args = List.map (xmap (fun x -> Var x)) case.args in
              let lhs =
                To_pat.term_to_pattern (AppOp (case.constructor, args)) #: None
              in
              {
                pc_lhs = lhs;
                pc_guard = None;
                pc_rhs = expr_to_ocamlexpr case.exp;
              })
            cs
        in
        Pexp_match (case_target, cases)
    | Lam { lamarg; lambody } ->
        Pexp_fun
          ( Asttypes.Nolabel,
            None,
            To_pat.typed_ids_to_pattern [ lamarg ],
            expr_to_ocamlexpr lambody )
  in
  aux expr

and hd_case_aux { effop; effk; effargs; hbody } =
  let name = mk_idloc [ String.uncapitalize_ascii effop.x ] in
  let args = effk :: effargs in
  let lam = curry (args, hbody) in
  (name, expr_to_ocamlexpr lam)

and ret_case_aux { retarg; retbody } =
  let name = mk_idloc [ String.uncapitalize_ascii kw_retc ] in
  let lam = curry ([ retarg ], retbody) in
  (name, expr_to_ocamlexpr lam)

and hd_aux { ret_case; handler_cases } =
  Pexp_record (ret_case_aux ret_case :: List.map hd_case_aux handler_cases, None)

open Sugar

let expr_of_ocamlexpr expr =
  let handle_id id =
    match Longident.flatten id.Location.txt with
    | [ x ] -> x
    | ids ->
        failwith
          (Printf.sprintf "expr, handel id: %s"
          @@ Zzdatatype.Datatype.StrList.to_string ids)
  in
  let id_to_var id = xmap (fun x -> Var x) id in
  let update_ty { x; ty } ty' =
    match ty with None -> x #: (Some ty') | Some _ -> x #: (Some ty')
    (* NOTE: the type denotation is stronger than type inference *)
  in
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_tuple es -> (Tu (List.map aux es)) #: None
    | Pexp_constraint (expr, ty) ->
        let ty = Type.core_type_to_t ty in
        update_ty (aux expr) ty
    | Pexp_ident id -> id_to_var @@ ((handle_id id) #: None)
    | Pexp_construct (c, args) -> (
        (* let () = *)
        (*   Printf.printf "check op: %s\n" (Pprintast.string_of_expression expr) *)
        (* in *)
        let c = To_pat.constructor_to_term_or_pmop @@ handle_id c in
        (* let () = Printf.printf "Pat: %s\n" c in *)
        match c with
        | To_pat.C_is_term tm -> tm
        | To_pat.C_is_pmop pmop -> (
            match args with
            | None -> (AppOp (pmop, [])) #: None
            | Some args -> (
                let args = aux args in
                match args.x with
                | Tu es -> (AppOp (pmop, es)) #: None
                | _ -> (AppOp (pmop, [ args ])) #: None)))
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
                | AppOp ({ x = DtConstructor opname; ty }, rhsargs) ->
                    (Perform { rhsop = { x = opname; ty }; rhsargs }) #: res.ty
                | _ -> _failatwith __FILE__ __LINE__ "Syntax Error: perform")
            | _ -> _failatwith __FILE__ __LINE__ "Syntax Error: perform")
        | Var name when String.equal name kw_match_with -> (
            match args with
            | [ (_, handled_prog); (_, hd) ] ->
                let handled_prog = aux handled_prog in
                let handler = hd_aux hd in
                (CWithH { handler; handled_prog }) #: None
            | _ -> _failatwith __FILE__ __LINE__ "Syntax Error: perform")
        | _ -> (App (func, List.map (fun x -> aux @@ snd x) args)) #: None)
    | Pexp_ifthenelse (e1, e2, Some e3) ->
        (Ite (aux e1, aux e2, aux e3)) #: None
    | Pexp_ifthenelse (_, _, None) -> raise @@ failwith "no else branch in ite"
    | Pexp_match (case_target, cases) ->
        let cs =
          List.map
            (fun case ->
              match (To_pat.pattern_to_term case.pc_lhs).x with
              | AppOp (pmop, args) ->
                  {
                    constructor = pmop;
                    args = List.map to_var args;
                    exp = aux case.pc_rhs;
                  }
              | _ -> _failatwith __FILE__ __LINE__ "?")
            cases
        in
        (Match (aux case_target, cs)) #: None
    | Pexp_fun (_, _, arg, expr) ->
        let arg = To_pat.pattern_to_term arg in
        let () =
          match arg.ty with
          | None ->
              failwith "Syntax error: lambda function should provide types"
          | Some _ -> ()
        in
        let lamarg =
          match arg.x with
          | Var x -> x #: arg.ty
          | _ -> failwith "Syntax error: lambda function wrong argument"
        in
        (Lam { lamarg; lambody = aux expr }) #: None
        (* un-curry *)
    | Pexp_record (_, _) ->
        let res = hd_aux expr in
        (VHd res) #: res.ty
    | _ ->
        raise
        @@ failwith
             (Sugar.spf "not imp client parsing:%s"
             @@ Pprintast.string_of_expression expr)
  and hd_case_aux (name, expr) =
    let effop = (String.capitalize_ascii @@ handle_id name) #: None in
    let args, hbody = uncurry @@ aux expr in
    match args with
    | effk :: effargs -> { effop; effk; effargs; hbody }
    | _ -> _failatwith __FILE__ __LINE__ "?"
  and hd_aux expr : handler typed =
    match expr.pexp_desc with
    | Pexp_record (cases, None) -> (
        let l = List.map hd_case_aux cases in
        match List.partition (fun x -> String.equal kw_retc x.effop.x) l with
        | [ { effk; effargs = []; hbody; _ } ], handler_cases ->
            let ret_case = { retarg = effk; retbody = hbody } in
            { ret_case; handler_cases } #: None
        | _ -> _failatwith __FILE__ __LINE__ "Syntax Error: hd")
    | _ -> _failatwith __FILE__ __LINE__ "?"
  in
  aux expr

let layout x = Pprintast.string_of_expression @@ expr_to_ocamlexpr x

(* let prim_dt = [ "[]"; "::" ] *)
(* let is_prim_dt x = List.exists (String.equal x) prim_dt *)

(* let op_of_string_opt x = try Some (op_of_string x) with _ -> None *)
