module MetaEnv = Env
open Ocaml5_parser
open Parsetree
module Type = Normalty.Frontend
open Syntax
open RtyRaw.P
open Sugar

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

type layout_setting = {
  sym_true : string;
  sym_false : string;
  sym_and : string;
  sym_or : string;
  sym_not : string;
  sym_implies : string;
  sym_iff : string;
  sym_forall : string;
  sym_exists : string;
  layout_typedid : string Nt.typed -> string;
  layout_mp : string -> string;
}

open Zzdatatype.Datatype

let detailssetting =
  {
    sym_true = "⊤";
    sym_false = "⊥";
    sym_and = " ∧ ";
    sym_or = " ∨ ";
    sym_not = "¬";
    sym_implies = "=>";
    sym_iff = "<=>";
    sym_forall = "∀";
    sym_exists = "∃";
    layout_typedid = Nt.(fun x -> spf "(%s:%s)" x.x (layout x.ty));
    layout_mp = (fun x -> x);
  }

let psetting =
  {
    sym_true = "⊤";
    sym_false = "⊥";
    sym_and = " ∧ ";
    sym_or = " ∨ ";
    sym_not = "¬";
    sym_implies = "=>";
    sym_iff = "<=>";
    sym_forall = "∀";
    sym_exists = "∃";
    layout_typedid = (fun x -> x.x);
    (* (fun x ->          Printf.spf "(%s:%s)" x.x (Ty.layout x.ty)); *)
    layout_mp = (fun x -> x);
  }

let coqsetting =
  {
    sym_true = "True";
    sym_false = "False";
    sym_and = "/\\ ";
    sym_or = " \\/ ";
    sym_not = "~";
    sym_implies = "->";
    sym_iff = "<->";
    sym_forall = "forall";
    sym_exists = "exists";
    layout_typedid = (fun x -> x.x);
    layout_mp = (function "==" -> "=" | x -> x);
  }

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
    | Lit lit -> To_lit.layout_lit lit
    | Implies (p1, p2) -> spf "(%s %s %s)" (layout p1) sym_implies (layout p2)
    | And ps -> spf "(%s)" @@ List.split_by sym_and layout ps
    | Or ps -> spf "(%s)" @@ List.split_by sym_or layout ps
    | Not p -> spf "(%s %s)" sym_not @@ layout p
    | Iff (p1, p2) -> spf "(%s %s %s)" (layout p1) sym_iff (layout p2)
    | Ite (p1, p2, p3) ->
        spf "(if %s then %s else %s)" (layout p1) (layout p2) (layout p3)
    | Forall (u, body) ->
        spf "(%s%s. %s)" sym_forall (layout_typedid u) (layout body)
    | Exists (u, body) ->
        spf "(%s%s. %s)" sym_exists (layout_typedid u) (layout body)
  in
  layout

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
  | Ppat_constraint (arg, ct) -> (
      let arg =
        match arg.ppat_desc with
        | Ppat_var arg -> arg.txt
        | _ -> failwith "parsing: prop function"
      in
      match ct.ptyp_desc with
      | Ptyp_extension (name, PTyp ty) ->
          let q = Qn.of_string name.txt in
          let ty = Type.core_type_to_t ty in
          (q, Nt.(arg #: ty))
      | _ -> _failatwith __FILE__ __LINE__ "quantifier needs type extension")
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

let layout_lit = To_lit.layout_lit
let layout_typed_lit = To_lit.layout_typed_lit
let layout_raw x = Pprintast.string_of_expression @@ qualifier_to_ocamlexpr x
let layout = layout_qualifier psetting
