module MetaEnv = Env
open Ocaml_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module NTyped = Normalty.Ntyped
open Ast.QualifierRaw
open Sugar

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

let id_to_ocamlexpr id = desc_to_ocamlexpr @@ Pexp_ident (mk_idloc [ id.x ])

let rec lit_to_ocamlexpr expr = desc_to_ocamlexpr @@ lit_to_ocamlexpr_desc expr

and lit_to_ocamlexpr_desc expr =
  let aux expr =
    match expr with
    | AC c -> (To_const.value_to_expr c).pexp_desc
    | AApp (op, args) when String.equal op.x f_pair ->
        let () =
          _assert __FILE__ __LINE__ "need to be pair" (2 == List.length args)
        in
        Pexp_tuple (List.map lit_to_ocamlexpr args)
    | AApp (func, args) ->
        let func = id_to_ocamlexpr func in
        let args =
          List.map (fun x -> (Asttypes.Nolabel, lit_to_ocamlexpr x)) args
        in
        Pexp_apply (func, args)
    | APair (a, b) -> Pexp_tuple [ lit_to_ocamlexpr a; lit_to_ocamlexpr b ]
    | AFst a ->
        let a = (Asttypes.Nolabel, lit_to_ocamlexpr a) in
        Pexp_apply (desc_to_ocamlexpr @@ Pexp_ident (mk_idloc [ f_fst ]), [ a ])
    | ASnd a ->
        let a = (Asttypes.Nolabel, lit_to_ocamlexpr a) in
        Pexp_apply (desc_to_ocamlexpr @@ Pexp_ident (mk_idloc [ f_snd ]), [ a ])
    | AVar x -> (id_to_ocamlexpr x).pexp_desc
  in
  aux expr

let typed_to_ocamlexpr_desc f expr =
  match expr.ty with
  | None -> f expr.x
  | Some ty ->
      Pexp_constraint (desc_to_ocamlexpr @@ f expr.x, Type.t_to_core_type ty)

let notated (name, t) =
  Type.desc_to_ct
  @@ Ptyp_extension (Location.mknoloc name, PTyp (Type.t_to_core_type t))

let quantifier_to_patten (q, u) =
  To_pat.dest_to_pat
    (Ppat_constraint
       ( To_pat.dest_to_pat (Ppat_var (Location.mknoloc u.NTyped.x)),
         notated (Q.to_string q, u.NTyped.ty) ))

let rec qualifier_to_ocamlexpr expr =
  desc_to_ocamlexpr @@ qualifier_to_ocamlexpr_desc expr

and qualifier_to_ocamlexpr_desc expr =
  let rec aux e =
    let labeled x = (Asttypes.Nolabel, qualifier_to_ocamlexpr x) in
    match e with
    | Lit lit -> lit_to_ocamlexpr_desc lit
    | MethodPred (mp, args) ->
        Pexp_apply
          ( id_to_ocamlexpr mp,
            List.map (fun x -> (Asttypes.Nolabel, lit_to_ocamlexpr x)) args )
    | Implies (e1, e2) ->
        Pexp_apply
          (id_to_ocamlexpr "implies" #: None, List.map labeled [ e1; e2 ])
    | Ite (e1, e2, e3) ->
        Pexp_ifthenelse
          ( qualifier_to_ocamlexpr e1,
            qualifier_to_ocamlexpr e2,
            Some (qualifier_to_ocamlexpr e3) )
    | Not e -> Pexp_apply (id_to_ocamlexpr "not" #: None, List.map labeled [ e ])
    | And [] -> failwith "un-imp"
    | And [ x ] -> aux x
    | And (h :: t) ->
        Pexp_apply (id_to_ocamlexpr "&&" #: None, List.map labeled [ h; And t ])
    | Or [] -> failwith "un-imp"
    | Or [ x ] -> aux x
    | Or (h :: t) ->
        Pexp_apply (id_to_ocamlexpr "||" #: None, List.map labeled [ h; Or t ])
    | Iff (e1, e2) ->
        Pexp_apply (id_to_ocamlexpr "iff" #: None, List.map labeled [ e1; e2 ])
    | Forall (u, body) ->
        Pexp_fun
          ( Asttypes.Nolabel,
            None,
            quantifier_to_patten (Q.Fa, u),
            qualifier_to_ocamlexpr body )
    | Exists (u, body) ->
        Pexp_fun
          ( Asttypes.Nolabel,
            None,
            quantifier_to_patten (Q.Ex, u),
            qualifier_to_ocamlexpr body )
  in
  aux expr

let handle_id id =
  match Longident.flatten id.Location.txt with
  | [ x ] -> x #: None
  | ids ->
      failwith
        (Printf.sprintf "expr, handel id: %s"
        @@ Zzdatatype.Datatype.StrList.to_string ids)

let id_to_ocamlexpr func =
  match func.pexp_desc with
  | Pexp_ident id -> handle_id id
  | _ ->
      failwith
        (spf "wrong lit function: %s" @@ Pprintast.string_of_expression func)

let rec lit_of_ocamlexpr e =
  match e.pexp_desc with
  | Pexp_ident id -> AVar (handle_id id)
  | Pexp_constant _ | Pexp_construct _ -> AC (To_const.expr_to_value e)
  | Pexp_apply (func, args) -> (
      let args = List.map (fun x -> lit_of_ocamlexpr @@ snd x) args in
      let f = id_to_ocamlexpr func in
      match f.x with
      | x when String.equal x f_fst -> (
          match args with
          | [ a ] -> AFst a
          | _ -> _failatwith __FILE__ __LINE__ "wrong fst")
      | x when String.equal x f_snd -> (
          match args with
          | [ a ] -> ASnd a
          | _ -> _failatwith __FILE__ __LINE__ "wrong snd")
      | _ -> AApp (f, args))
  | Pexp_tuple es -> (
      match es with
      | [ a; b ] -> APair (lit_of_ocamlexpr a, lit_of_ocamlexpr b)
      | _ -> _failatwith __FILE__ __LINE__ "need to be pair")
  | _ ->
      failwith
      @@ Printf.sprintf "parsing: not a op (%s)"
      @@ Pprintast.string_of_expression e

let is_mp x =
  let c = Char.code (String.get x.x 0) in
  (* let () = Printf.printf "%s: %i\n" x.x c in *)
  c == 95
(* 65 <= c && c <= 90 *)

let quantifier_of_ocamlexpr arg =
  match arg.ppat_desc with
  | Ppat_constraint (arg, ct) -> (
      let arg =
        match arg.ppat_desc with
        | Ppat_var arg -> arg.txt
        | _ -> failwith "parsing: prop function"
      in
      match ct.ptyp_desc with
      | Ptyp_extension (name, PTyp ty) ->
          let q = Q.of_string name.txt in
          let ty = Type.core_type_to_t ty in
          (q, NTyped.(arg #: ty))
      | _ -> _failatwith __FILE__ __LINE__ "quantifier needs type extension")
  | _ -> _failatwith __FILE__ __LINE__ "quantifier needs type notation"

let qualifier_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ -> failwith "parsing: qualifier does not have type"
    | Pexp_tuple _ | Pexp_ident _ | Pexp_constant _ | Pexp_construct _ ->
        Lit (lit_of_ocamlexpr expr)
    | Pexp_let _ -> failwith "parsing: qualifier does not have let"
    | Pexp_apply (func, args) -> (
        let f = id_to_ocamlexpr func in
        if is_mp f then
          let args = List.map (fun x -> lit_of_ocamlexpr @@ snd x) args in
          MethodPred (f, args)
        else
          let args = List.map snd args in
          match (f.x, args) with
          | "not", [ e1 ] -> Not (aux e1)
          | "not", _ -> failwith "parsing: qualifier wrong not"
          | "ite", [ e1; e2; e3 ] -> Ite (aux e1, aux e2, aux e3)
          | "ite", _ -> failwith "parsing: qualifier wrong ite"
          | "implies", [ e1; e2 ] -> Implies (aux e1, aux e2)
          | "implies", _ -> failwith "parsing: qualifier wrong implies"
          | "iff", [ e1; e2 ] -> Iff (aux e1, aux e2)
          | "iff", _ -> failwith "parsing: qualifier wrong iff"
          | "&&", [ a; b ] -> And [ aux a; aux b ]
          | "&&", _ -> failwith "parsing: qualifier wrong and"
          | "||", [ a; b ] -> Or [ aux a; aux b ]
          | "||", _ -> failwith "parsing: qualifier wrong or"
          | "=", _ -> failwith "please use == instead of = "
          | _, _ -> Lit (lit_of_ocamlexpr expr))
    | Pexp_ifthenelse (e1, e2, Some e3) -> Ite (aux e1, aux e2, aux e3)
    | Pexp_ifthenelse (_, _, None) -> raise @@ failwith "no else branch in ite"
    | Pexp_match _ -> failwith "parsing: qualifier does not have match"
    | Pexp_fun (_, _, arg, expr) -> (
        let q, arg = quantifier_of_ocamlexpr arg in
        let body = aux expr in
        match q with Q.Fa -> Forall (arg, body) | Q.Ex -> Exists (arg, body))
    | _ ->
        raise
        @@ failwith
             (Printf.sprintf "not imp client parsing:%s"
             @@ Pprintast.string_of_expression expr)
  in
  aux expr

let layout_lit x = Pprintast.string_of_expression @@ lit_to_ocamlexpr x
let layout x = Pprintast.string_of_expression @@ qualifier_to_ocamlexpr x
