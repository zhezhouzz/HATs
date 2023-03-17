module MetaEnv = Env
open Ocaml_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module L = Ast.Termlang

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
  match expr.L.ty with
  | None -> expr_to_ocamlexpr_desc expr.L.x
  | Some ty ->
      Pexp_constraint
        ( desc_to_ocamlexpr @@ expr_to_ocamlexpr_desc expr.L.x,
          Type.notated_t_to_core_type ty )

and expr_to_ocamlexpr_desc expr =
  let aux expr =
    match expr with
    | L.Exn -> Pexp_ident (mk_idloc [ "Exn" ])
    | L.Tu es -> Pexp_tuple (List.map expr_to_ocamlexpr es)
    | L.Var var -> Pexp_ident (mk_idloc [ var ])
    | L.Const v -> (Value.value_to_expr v).pexp_desc
    | L.Let (_, [], _, _) -> failwith "die"
    | L.Let (if_rec, names, e, body) ->
        let flag =
          if if_rec then Asttypes.Recursive else Asttypes.Nonrecursive
        in
        let vb =
          {
            pvb_pat =
              Pat.slang_to_pattern
                L.(
                  make_untyped
                  @@ Tu
                       (List.map
                          (fun (ty, id) -> { ty = Some ty; x = Var id })
                          names));
            pvb_expr = expr_to_ocamlexpr e;
            pvb_attributes = [];
            pvb_loc = Location.none;
          }
        in
        Pexp_let (flag, [ vb ], expr_to_ocamlexpr body)
    | L.App (func, args) ->
        let func = expr_to_ocamlexpr func in
        let args =
          List.map (fun x -> (Asttypes.Nolabel, expr_to_ocamlexpr x)) args
        in
        Pexp_apply (func, args)
    | L.Op (op, args) ->
        let func =
          expr_to_ocamlexpr L.{ ty = None; x = Var (Op.T.op_to_string op) }
        in
        let args =
          List.map (fun x -> (Asttypes.Nolabel, expr_to_ocamlexpr x)) args
        in
        Pexp_apply (func, args)
    | L.Ite (e1, e2, e3) ->
        let e1, e2, e3 = Sugar.map3 expr_to_ocamlexpr (e1, e2, e3) in
        Pexp_ifthenelse (e1, e2, Some e3)
    | L.Match (case_target, cs) ->
        let case_target = expr_to_ocamlexpr case_target in
        let cases =
          List.map
            (fun case ->
              {
                pc_lhs =
                  Pat.slang_to_pattern
                    L.(make_untyped_id_app (case.L.constructor.x, case.L.args));
                pc_guard = None;
                pc_rhs = expr_to_ocamlexpr case.L.exp;
              })
            cs
        in
        Pexp_match (case_target, cases)
    | L.Lam (ty, x, rankfunc, body) ->
        let ext =
          match rankfunc with
          | None -> []
          | Some (name, lit) ->
              [
                {
                  attr_name = Location.mknoloc "rankfunc";
                  attr_payload =
                    PPat
                      ( Pat.dest_to_pat (Ppat_var (Location.mknoloc name)),
                        Some (Autov.lit_to_ocamlexpr lit) );
                  attr_loc = Location.none;
                };
              ]
        in
        let flag = Asttypes.Nolabel in
        (* let body = *)
        (*   let e = expr_to_ocamlexpr body in *)
        (*   match body.L.ty with *)
        (*   | None -> e *)
        (*   | Some tp -> *)
        (*       desc_to_ocamlexpr @@ Pexp_constraint (e, Type.t_to_core_type tp) *)
        (* in *)
        Pexp_fun
          ( flag,
            None,
            {
              (Pat.slang_to_pattern L.{ ty = Some ty; x = Var x }) with
              ppat_attributes = ext;
            },
            expr_to_ocamlexpr body )
    (* | L.Lam (x :: t, body) -> *)
    (*     let flag = Asttypes.Nolabel in *)
    (*     Pexp_fun *)
    (*       ( flag, *)
    (*         None, *)
    (*         Pat.slang_to_pattern (L.typedstr_to_var x), *)
    (*         expr_to_ocamlexpr @@ L.make_untyped @@ L.Lam (t, body) ) *)
  in
  aux expr

let handle_case_v1 case =
  match case.pc_guard with
  | None ->
      ( MetaEnv.show_debug_info @@ fun _ ->
        Printf.printf "%s\n" @@ Pprintast.string_of_expression case.pc_rhs );
      failwith "handle_case"
  | Some guard -> (guard, case.pc_rhs)

let handle_case_v2 case =
  let l = Pat.pattern_to_slang case.pc_lhs in
  (l, case.pc_rhs)

let expr_of_ocamlexpr expr =
  let handle_id id =
    match Longident.flatten id.Location.txt with
    | [ x ] -> x
    | ids ->
        failwith
          (Printf.sprintf "expr, handel id: %s"
          @@ Zzdatatype.Datatype.StrList.to_string ids)
  in
  let id_to_var id = L.(make_untyped @@ Var (handle_id id)) in
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_tuple es -> L.(make_untyped @@ Tu (List.map aux es))
    | Pexp_constraint (expr, ty) -> (
        let e = aux expr in
        let ty = Type.core_type_to_t ty in
        L.(
          match e.ty with
          | None -> { ty = Some (None, ty); x = e.x }
          | Some _ -> failwith "multi typed"))
    | Pexp_ident id -> id_to_var id
    | Pexp_construct (c, args) -> (
        (* let () = *)
        (*   Printf.printf "check op: %s\n" (Pprintast.string_of_expression expr) *)
        (* in *)
        let c = handle_id c in
        (* let () = Printf.printf "Pat: %s\n" c in *)
        match c with
        | "Exn" -> L.{ ty = Some (None, Ty_unknown); x = Exn }
        | "true" -> L.{ ty = Some (None, Ty_bool); x = Const (Value.V.B true) }
        | "false" ->
            L.{ ty = Some (None, Ty_bool); x = Const (Value.V.B false) }
        | _ -> (
            let c = L.(make_untyped @@ Var c) in
            match args with
            | None -> handle_app c []
            | Some args -> (
                let args = aux args in
                match args.x with
                | L.Var _ -> handle_app c [ args ]
                | L.Tu es -> handle_app c es
                | _ -> failwith "die")))
    | Pexp_constant _ -> L.(make_untyped @@ Const (Value.expr_to_value expr))
    | Pexp_let (flag, vbs, e) ->
        List.fold_right
          (fun vb body ->
            let leftvar = Pat.pattern_to_slang vb.pvb_pat in
            let leftvars = Pat.to_typed_slang leftvar in
            let leftvars =
              List.map
                L.(
                  fun x ->
                    match x.ty with
                    | None ->
                        failwith
                          "Syntax error: let binding should provide types"
                    | Some ty -> (ty, x.x))
                leftvars
            in
            (* let _ = *)
            (*   Printf.printf "leftvar: %s --> %s\n" (Pat.layout_ vb.pvb_pat) *)
            (*     (List.split_by_comma *)
            (*        (fun x -> *)
            (*          Printf.sprintf "%s:%s" x.L.x *)
            (*            (match x.ty with *)
            (*            | None -> "none" *)
            (*            | Some ty -> Type.layout ty)) *)
            (*        leftvars) *)
            (* in *)
            L.(
              make_untyped
              @@ Let (get_if_rec flag, leftvars, aux vb.pvb_expr, body)))
          vbs (aux e)
    | Pexp_apply (func, args) ->
        let args = List.map (fun x -> aux @@ snd x) args in
        handle_app (aux func) args
    | Pexp_ifthenelse (e1, e2, Some e3) ->
        L.(make_untyped @@ Ite (aux e1, aux e2, aux e3))
    | Pexp_ifthenelse (_, _, None) -> raise @@ failwith "no else branch in ite"
    | Pexp_match (case_target, cases) ->
        let get_constructor x =
          match L.term_to_string_opt x with
          | Some x -> (x, [])
          | None -> (
              match x.x with
              | L.App (id, ids) -> (
                  match
                    (L.term_to_string_opt id, L.terms_to_strings_opt ids)
                  with
                  | Some id, Some ids -> (id, ids)
                  | _ -> failwith "pexp match")
              | _ -> failwith "pexp match")
        in
        (* let handle_match_args match_arg = *)
        (*   let e = aux match_arg in *)
        (*   let rec aux e = *)
        (*     match e with *)
        (*     | L.Var (_, var) -> [ var ] *)
        (*     | L.Tu vars -> List.flatten @@ List.map aux vars *)
        (*     | _ -> failwith "parser: wrong format in match" *)
        (*   in *)
        (*   aux e *)
        (* in *)
        (* let case_target = handle_match_args case_target in *)
        let cs =
          List.map
            (fun case ->
              let exp = aux case.pc_rhs in
              let pat = Pat.pattern_to_slang case.pc_lhs in
              let constructor, args = get_constructor pat in
              L.{ constructor = { ty = None; x = constructor }; args; exp })
            cases
        in
        L.(make_untyped @@ Match (aux case_target, cs))
    | Pexp_fun (_, _, arg, expr) ->
        (* let () = Printf.printf "has ext: %s\n" (Pat.layout_ arg) in *)
        let rank_func =
          match arg.ppat_attributes with
          | [] -> None
          | [ x ] when String.equal x.attr_name.txt "rankfunc" -> (
              match x.attr_payload with
              | PPat (pat, Some expr) -> (
                  match (pat.ppat_desc, expr.pexp_desc) with
                  | Ppat_var name, _ ->
                      Some (name.txt, Autov.lit_of_ocamlexpr expr)
                  | _ -> failwith "unknown extension")
              | _ -> failwith "unknown extension")
          | _ -> failwith "unknown extension"
        in
        let arg = Pat.pattern_to_slang arg in
        let ty =
          match arg.L.ty with
          | None ->
              failwith "Syntax error: lambda function should provide types"
          | Some ty -> ty
        in
        let x =
          match arg.L.x with
          | L.Var x -> x
          | _ -> failwith "Syntax error: lambda function wrong argument"
        in
        L.(make_untyped @@ Lam (ty, x, rank_func, aux expr))
        (* un-curry *)
    | _ ->
        raise
        @@ failwith
             (Sugar.spf "not imp client parsing:%s"
             @@ Pprintast.string_of_expression expr)
  and handle_app func args =
    let prim =
      match func.L.x with
      | L.Var prim -> Abstraction.Prim.normal_check_if_is_known_prims prim
      | _ -> None
    in
    match prim with
    | Some (Op.T.PrimOp op, _) -> L.(make_untyped @@ Op (op, args))
    | Some (Op.T.DtConstructor f, _) | Some (Op.T.External f, _) ->
        L.(make_untyped @@ App ({ x = Var f; ty = None }, args))
    | None -> L.(make_untyped @@ App (func, args))
  in
  aux expr

let layout x = Pprintast.string_of_expression @@ expr_to_ocamlexpr x

(* let prim_dt = [ "[]"; "::" ] *)
(* let is_prim_dt x = List.exists (String.equal x) prim_dt *)

(* let op_of_string_opt x = try Some (op_of_string x) with _ -> None *)
