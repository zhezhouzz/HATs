open Ocaml5_parser
open Parsetree
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.StructureRaw
open Sugar

let mk_rty_entry (x, name, pvb_expr) =
  let name =
    match x with
    | "effSRLRty" | "effRty" -> String.capitalize_ascii name
    | _ -> name
  in
  let kind =
    match x with "assertSRLRty" | "assertRty" -> RtyToCheck | _ -> RtyLib
  in
  match x with
  | "libSRLRty" | "effSRLRty" | "assertSRLRty" ->
      let rty = To_rty.rty_of_ocamlexpr pvb_expr in
      Rty { name; kind; rty }
  | _ ->
      let rty = To_ltlf_hty.rty_of_ocamlexpr pvb_expr in
      LtlfRty { name; kind; rty }

let mk_pred_args expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_fun (_, _, arg0, body) ->
        let args, body = aux body in
        let arg =
          match To_pat.patten_to_typed_ids arg0 with
          | [ { x; ty = Some ty } ] -> Nt.{ x; ty }
          | _ -> _failatwith __FILE__ __LINE__ "die"
        in
        (arg :: args, body)
    | _ -> ([], expr)
  in
  let args, body = aux expr in
  (args, body)

let ocaml_structure_to_structure structure =
  match structure.pstr_desc with
  | Pstr_primitive { pval_name; pval_type; _ } ->
      (* if String.equal pval_name.txt "method_predicates" then Mps pval_prim *)
      (* else *)
      Func_dec
        Normalty.Ntyped.(pval_name.txt #: (Type.core_type_to_t pval_type))
  | Pstr_type (_, [ type_dec ]) ->
      Type_dec (To_type_dec.of_ocamltypedec type_dec)
  | Pstr_value (flag, [ value_binding ]) -> (
      let name =
        match (To_pat.pattern_to_term value_binding.pvb_pat).x with
        | Var name -> name
        | _ -> failwith "die"
      in
      match value_binding.pvb_attributes with
      | [ x ] -> (
          let label = x.attr_name.txt in
          match label with
          | "axiom" ->
              let body =
                To_qualifier.qualifier_of_ocamlexpr value_binding.pvb_expr
              in
              Axiom (R.Ax.mk_ax (name, body))
          | "pred" ->
              let args, body = mk_pred_args value_binding.pvb_expr in
              LtlfPred { name; args; ltlf_body = To_ltlf.of_ocamlexpr body }
          | "SRLpred" ->
              let args, body = mk_pred_args value_binding.pvb_expr in
              SrlPred { name; args; srl_body = To_srl.of_ocamlexpr body }
          | "effRty" | "libRty" | "assertRty" | "libSRLRty" | "effSRLRty"
          | "assertSRLRty" ->
              mk_rty_entry (label, name, value_binding.pvb_expr)
          | _ ->
              _failatwith __FILE__ __LINE__
                "syntax error: non known rty kind, not libSRLRty / effSRLRty / \
                 effRty / assertRty / assertSRLRty / assertRty / pred / \
                 SRLpred / axiom")
      | [] ->
          let body = To_expr.expr_of_ocamlexpr value_binding.pvb_expr in
          FuncImp { name; if_rec = To_expr.get_if_rec flag; body }
      | _ -> _failatwith __FILE__ __LINE__ "wrong syntax")
  | _ -> _failatwith __FILE__ __LINE__ "translate not a func_decl"

open Zzdatatype.Datatype

let layout_entry = function
  | Type_dec d -> To_type_dec.layout [ d ]
  | Func_dec x ->
      let open Normalty.Ntyped in
      spf "val %s: %s" x.x @@ Type.layout x.ty
  | FuncImp { name; if_rec; body } ->
      spf "let %s%s = %s"
        (if if_rec then "rec " else "")
        name (To_expr.layout body)
  | Axiom { name; body; _ } ->
      spf "let[@axiom] %s = %s" name (To_qualifier.layout body)
  | Rty { name; kind; rty } ->
      spf "val[@%s] %s: %s"
        (match kind with RtyLib -> "libSRLRty" | RtyToCheck -> "assertSRLRty")
        name (To_rty.pprint_rty rty)
  | LtlfRty { name; kind; rty } ->
      spf "val[@%s] %s: %s"
        (match kind with RtyLib -> "libRty" | RtyToCheck -> "assertRty")
        name
        (To_ltlf_hty.pprint_rty rty)
  | LtlfPred { name; args; ltlf_body } ->
      spf "val[@pred] %s: %s = %s" name
        (List.split_by " "
           Nt.(fun x -> spf "(%s : %s)" x.x (layout x.Nt.ty))
           args)
        (To_ltlf.layout ltlf_body)
  | SrlPred { name; args; srl_body } ->
      spf "val[@SRLpred] %s: %s = %s" name
        (List.split_by " " Nt.(fun x -> spf "(%s : %s)" x.x (layout x.ty)) args)
        (To_srl.layout srl_body)

let layout l = spf "%s\n" (List.split_by "\n" layout_entry l)
