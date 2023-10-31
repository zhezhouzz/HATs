module MetaEnv = Env
open Ocaml5_parser
open Parsetree
module Type = Normalty.Frontend
open Syntax
open RtyRaw.P
open Sugar
open Aux

let typed_to_ocamlexpr_desc f expr =
  match expr.ty with
  | None -> f expr.x
  | Some ty ->
      Pexp_constraint
        (To_expr.desc_to_ocamlexpr @@ f expr.x, Type.t_to_core_type ty)

let notated (name, t) =
  Type.desc_to_ct
  @@ Ptyp_extension (Location.mknoloc name, PTyp (Type.t_to_core_type t))

let quantifier_to_patten (q, u) =
  To_pat.dest_to_pat
    (Ppat_constraint
       ( To_pat.dest_to_pat (Ppat_var (Location.mknoloc u.Nt.x)),
         notated (Qn.to_string q, u.Nt.ty) ))

open Zzdatatype.Datatype

let layout_qualifier
    {
      sym_and;
      sym_or;
      sym_not;
      sym_implies;
      sym_iff;
      sym_forall;
      sym_exists;
      layout_typedid;
      _;
    } =
  let rec layout = function
    | Lit lit -> (To_lit.layout lit, true)
    | Implies (p1, p2) ->
        (spf "%s %s %s" (p_layout p1) sym_implies (p_layout p2), false)
    | And [ p ] -> layout p
    | Or [ p ] -> layout p
    | And [ p1; p2 ] -> (spf "%s%s%s" (p_layout p1) sym_and (p_layout p2), false)
    | Or [ p1; p2 ] -> (spf "%s%s%s" (p_layout p1) sym_or (p_layout p2), false)
    | And ps -> (spf "%s" @@ List.split_by sym_and p_layout ps, false)
    | Or ps -> (spf "%s" @@ List.split_by sym_or p_layout ps, false)
    | Not p -> (spf "%s%s" sym_not (p_layout p), true)
    | Iff (p1, p2) -> (spf "%s %s %s" (p_layout p1) sym_iff (p_layout p2), false)
    | Ite (p1, p2, p3) ->
        ( spf "if %s then %s else %s"
            (fst @@ layout p1)
            (fst @@ layout p2)
            (fst @@ layout p3),
          false )
    | Forall (u, body) ->
        (spf "%s%s. %s" sym_forall (layout_typedid u) (p_layout body), false)
    | Exists (u, body) ->
        (spf "%s%s. %s" sym_exists (layout_typedid u) (p_layout body), false)
  and p_layout p =
    match layout p with str, true -> str | str, false -> spf "(%s)" str
  in
  fun a -> fst @@ layout a

let rec qualifier_to_ocamlexpr expr =
  To_expr.desc_to_ocamlexpr @@ qualifier_to_ocamlexpr_desc expr

and qualifier_to_ocamlexpr_desc expr =
  let rec aux e =
    let labeled x = (Asttypes.Nolabel, qualifier_to_ocamlexpr x) in
    match e with
    | Lit lit -> To_lit.lit_to_ocamlexpr_desc lit
    | Implies (e1, e2) ->
        Pexp_apply
          (To_expr.id_to_ocamlexpr "implies", List.map labeled [ e1; e2 ])
    | Ite (e1, e2, e3) ->
        Pexp_ifthenelse
          ( qualifier_to_ocamlexpr e1,
            qualifier_to_ocamlexpr e2,
            Some (qualifier_to_ocamlexpr e3) )
    | Not e -> Pexp_apply (To_expr.id_to_ocamlexpr "not", List.map labeled [ e ])
    | And [] -> failwith "un-imp"
    | And [ x ] -> aux x
    | And (h :: t) ->
        Pexp_apply (To_expr.id_to_ocamlexpr "&&", List.map labeled [ h; And t ])
    | Or [] -> failwith "un-imp"
    | Or [ x ] -> aux x
    | Or (h :: t) ->
        Pexp_apply (To_expr.id_to_ocamlexpr "||", List.map labeled [ h; Or t ])
    | Iff (e1, e2) ->
        Pexp_apply (To_expr.id_to_ocamlexpr "iff", List.map labeled [ e1; e2 ])
    | Forall (u, body) ->
        Pexp_fun
          ( Asttypes.Nolabel,
            None,
            quantifier_to_patten (Qn.Fa, u),
            qualifier_to_ocamlexpr body )
    | Exists (u, body) ->
        Pexp_fun
          ( Asttypes.Nolabel,
            None,
            quantifier_to_patten (Qn.Ex, u),
            qualifier_to_ocamlexpr body )
  in
  aux expr

let quantifier_of_ocamlexpr arg =
  match arg.ppat_desc with
  | Ppat_constraint (arg, ct) ->
      let q =
        match get_pat_denoteopt arg with
        | None ->
            _failatwith __FILE__ __LINE__
              "quantifier needs be [@forall] or [@exists]"
        | Some q -> Qn.of_string q
      in
      let arg =
        match arg.ppat_desc with
        | Ppat_var arg -> arg.txt
        | _ -> failwith "parsing: prop function"
      in
      let ty = Type.core_type_to_t ct in
      (q, Nt.(arg #: ty))
  | _ -> _failatwith __FILE__ __LINE__ "quantifier needs type notation"

let qualifier_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ -> failwith "parsing: qualifier does not have type"
    | Pexp_let _ -> failwith "parsing: qualifier does not have let"
    | Pexp_match _ -> failwith "parsing: qualifier does not have match"
    | Pexp_apply (func, args) -> (
        let f = To_expr.id_of_ocamlexpr func in
        let args = List.map snd args in
        match (f, args) with
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
        | "=", _ -> failwith "please use == instead of ="
        | _, _ -> Lit (To_lit.lit_of_ocamlexpr expr))
    | Pexp_ifthenelse (e1, e2, Some e3) -> Ite (aux e1, aux e2, aux e3)
    | Pexp_ifthenelse (_, _, None) -> raise @@ failwith "no else branch in ite"
    | Pexp_fun (_, _, arg, expr) -> (
        let q, arg = quantifier_of_ocamlexpr arg in
        let body = aux expr in
        match q with Qn.Fa -> Forall (arg, body) | Qn.Ex -> Exists (arg, body))
    | Pexp_tuple _ | Pexp_ident _ | Pexp_constant _ | Pexp_construct _ ->
        Lit (To_lit.lit_of_ocamlexpr expr)
    | _ ->
        raise
        @@ failwith
             (spf "not imp client parsing:%s"
             @@ Pprintast.string_of_expression expr)
  in
  aux expr

(* let layout = To_lit.layout *)
(* let layout_typed_lit = To_lit.layout_typed_lit *)
let layout_raw x = Pprintast.string_of_expression @@ qualifier_to_ocamlexpr x
let layout = layout_qualifier psetting

let pprint v (phi : prop) =
  match phi with
  | Lit
      (AAppOp
        ( { x = Op.BuiltinOp "=="; _ },
          [ { x = AVar id; _ }; { x = AC (Constant.I i); _ } ] ))
    when String.equal v.Nt.x id ->
      spf "%i" i
  | Lit
      (AAppOp
        ( { x = Op.BuiltinOp "=="; _ },
          [ { x = AVar id; _ }; { x = AC (Constant.B b); _ } ] ))
    when String.equal v.Nt.x id ->
      spf "%b" b
  | _ -> layout phi
