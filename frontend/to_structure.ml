open Ocaml5_parser
open Parsetree
module Type = Normalty.Frontend
open Syntax.StructureRaw
open Sugar

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
      | [ x ] when String.equal x.attr_name.txt "librty" ->
          Rty
            {
              name;
              kind = RtyLib;
              rty = To_rty.rty_of_ocamlexpr value_binding.pvb_expr;
            }
      | [ x ] when String.equal x.attr_name.txt "effrty" ->
          Rty
            {
              name = String.capitalize_ascii name;
              kind = RtyLib;
              rty = To_rty.rty_of_ocamlexpr value_binding.pvb_expr;
            }
      | [ x ] when String.equal x.attr_name.txt "assert" ->
          Rty
            {
              name;
              kind = RtyToCheck;
              rty = To_rty.rty_of_ocamlexpr value_binding.pvb_expr;
            }
      (* | [ x ] when String.equal x.attr_name.txt "equation" -> *)
      (*     EquationEntry *)
      (*       (To_algebraic.equation_of_ocamlexpr value_binding.pvb_expr) *)
      | _ ->
          let body = To_expr.expr_of_ocamlexpr value_binding.pvb_expr in
          FuncImp { name; if_rec = To_expr.get_if_rec flag; body })
  | _ -> raise @@ failwith "translate not a func_decl"

open Zzdatatype.Datatype

let layout_entry = function
  (* | Mps mps -> *)
  (*     spf "external method_predicates : t = %s" *)
  (*       (List.split_by " " (fun x -> x) mps) *)
  | Type_dec d -> To_type_dec.layout [ d ]
  | Func_dec x ->
      let open Normalty.Ntyped in
      spf "val %s: %s" x.x @@ Type.layout x.ty
  | FuncImp { name; if_rec; body } ->
      spf "let %s%s = %s"
        (if if_rec then "rec " else "")
        name (To_expr.layout body)
  (* | EquationEntry equation -> To_algebraic.layout_equation equation *)
  | Rty { name; kind; rty } ->
      spf "val[@%s] %s: %s"
        (match kind with RtyLib -> "librty" | RtyToCheck -> "rty")
        name (To_rty.pprint_rty rty)

let layout l = spf "%s\n" (List.split_by "\n" layout_entry l)
