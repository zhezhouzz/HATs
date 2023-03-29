module MetaEnv = Env
open Ocaml_parser
open Parsetree

(* open Zzdatatype.Datatype *)
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Ast.RtyRaw
open Sugar

let pprint_id Nt.{ x; ty } = spf "%s:%s" x (Nt.layout ty)

let pprint_basety { h; v; phi } =
  let phi =
    let open P in
    match phi with
    | MethodPred ({ x = "=="; _ }, [ AVar id; AC (Constant.I i) ])
      when String.equal v.x id.x ->
        spf "%i" i
    | MethodPred ({ x = "=="; _ }, [ AVar id; AC (Constant.B b) ])
      when String.equal v.x id.x ->
        spf "%b" b
    | _ -> To_qualifier.layout phi
  in
  spf "%s | %s | %s" (pprint_id h) (pprint_id v) phi

let pprint_ou ou body =
  match ou with Over -> spf "{%s}" body | Under -> spf "[%s]" body

let pprint_label_arr l =
  let open Leff in
  match l with None -> "→" | Some EffArr -> "⇒" | Some HdArr -> "⇛"

let rec pprint_rty rty =
  match rty with
  | BaseRty { ou; basety } -> pprint_ou ou (pprint_basety basety)
  | DepRty { dep; label; rarg; retrty } -> (
      let x = match rarg.x with None -> "" | Some x -> spf "%s:" x in
      match dep with
      | Pi ->
          spf "%s%s%s%s" x (pprint_rty rarg.ty) (pprint_label_arr label)
            (pprint_rty retrty)
      | Sigma -> spf "(%s%s, %s)" x (pprint_rty rarg.ty) (pprint_rty retrty))

let get_ou expr =
  match expr.pexp_attributes with
  | [ x ] when String.equal x.attr_name.txt "over" -> Over
  | [ x ] when String.equal x.attr_name.txt "under" -> Under
  | _ -> _failatwith __FILE__ __LINE__ ""

let get_dep_label expr =
  match expr.pvb_attributes with
  | x :: rest ->
      let dep =
        match x.attr_name.txt with
        | "sigma" -> Sigma
        | "pi" -> Pi
        | _ -> _failatwith __FILE__ __LINE__ "wrong dependent mode"
      in
      let label =
        match rest with
        | [] -> None
        | [ x ] when String.equal x.attr_name.txt "eff" -> Some Leff.EffArr
        | [ x ] when String.equal x.attr_name.txt "hd" -> Some Leff.HdArr
        | _ -> _failatwith __FILE__ __LINE__ "wrong arrow kind"
      in
      (dep, label)
  | _ -> _failatwith __FILE__ __LINE__ ""

let get_self ct =
  let open Nt in
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> name.txt #: (Type.core_type_to_t ty)
  | _ -> _failatwith __FILE__ __LINE__ ""

let baserty_of_ocamlexpr expr =
  match expr.pexp_desc with
  | Pexp_constraint (e, ct) -> (
      let h = get_self ct in
      match e.pexp_desc with
      | Pexp_constraint (e', ct) ->
          let v = get_self ct in
          let phi = To_qualifier.qualifier_of_ocamlexpr e' in
          { h; v; phi }
      | _ -> _failatwith __FILE__ __LINE__ "")
  | _ -> _failatwith __FILE__ __LINE__ ""

let rty_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_let (_, [ vb ], body) ->
        let id = To_pat.patten_to_typed_ids vb.pvb_pat in
        let rx =
          match id with
          | [ id ] when String.equal id.x "_" -> None
          | [ id ] -> Some id.x
          | _ -> failwith "rty_of_ocamlexpr"
        in
        let rarg_rty = aux vb.pvb_expr in
        let rarg = rx #: rarg_rty in
        let dep, label = get_dep_label vb in
        DepRty { dep; label; rarg; retrty = aux body }
    | Pexp_constraint _ ->
        let ou = get_ou expr in
        BaseRty { ou; basety = baserty_of_ocamlexpr expr }
    | _ ->
        _failatwith __FILE__ __LINE__
          (spf "wrong refinement type: %s"
             (Pprintast.string_of_expression expr))
  in
  aux expr

let layout = pprint_rty
