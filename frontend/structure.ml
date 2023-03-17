open Ocaml_parser
open Parsetree
module L = Ast.Termlang
module S = Ast.Struc
module Type = Normalty.Frontend

let func_decl_of_ocamlstruct_one structure =
  match structure.pstr_desc with
  | Pstr_primitive { pval_name; pval_type; _ } ->
      (pval_name.txt, Type.core_type_to_t pval_type)
  | _ -> raise @@ failwith "translate not a func_decl"

let func_decl_of_ocamlstruct structures =
  List.map func_decl_of_ocamlstruct_one structures

let type_decl_of_ocamlstruct_one structure =
  match structure.pstr_desc with
  | Pstr_type (_, [ type_dec ]) -> Typedec.of_ocamltypedec type_dec
  | _ -> raise @@ failwith "translate not a type decl"

let type_decl_of_ocamlstruct structures =
  List.map type_decl_of_ocamlstruct_one structures

let mps_of_ocamlstruct_one structure =
  (* let () = *)
  (*   Printf.printf "mps_of_ocamlstruct_one: %s" *)
  (*   @@ Pprintast.string_of_structure [ structure ] *)
  (* in *)
  match structure.pstr_desc with
  | Pstr_primitive { pval_name; pval_prim; _ } ->
      if not (String.equal pval_name.txt "method_predicates") then
        failwith "\"external method_predicates : t = ...\" is expected"
      else
        (* let () = *)
        (*   Printf.printf "mps_of_ocamlstruct_one: %s\n" *)
        (*     (Zzdatatype.Datatype.StrList.to_string pval_prim) *)
        (* in *)
        pval_prim
  | _ -> raise @@ failwith "translate not a function value"

let client_of_ocamlstruct_one structure =
  match structure.pstr_desc with
  | Pstr_value (flag, [ value_binding ]) ->
      let name =
        match (Pat.pattern_to_slang value_binding.pvb_pat).x with
        | L.Var name -> name
        | _ -> failwith "die"
      in
      let body = Expr.expr_of_ocamlexpr value_binding.pvb_expr in
      Some S.{ name; if_rec = Expr.get_if_rec flag; body }
  | _ -> raise @@ failwith "translate not a function value"

let client_of_ocamlstruct structures =
  List.filter_map client_of_ocamlstruct_one structures

open Zzdatatype.Datatype
open Sugar
open S

let layout_one { name; if_rec; body } =
  spf "let %s%s = %s" (if if_rec then "rec " else "") name (Expr.layout body)

let layout l = spf "%s\n" (List.split_by "\n" layout_one l)

type ext =
  | NoExt
  | NotationExt of string
  | LibraryExt
  | Inv of (string * Autov.Prop.lit)

let refinement_of_ocamlstruct_one t_of_ocamlexpr structure =
  match structure.pstr_desc with
  | Pstr_value (_, [ value_binding ]) ->
      let a =
        match value_binding.pvb_attributes with
        | [ x ] when String.equal x.attr_name.txt "notation_over" ->
            NotationExt "over"
        | [ x ] when String.equal x.attr_name.txt "notation_under" ->
            NotationExt "under"
        | [ x ] when String.equal x.attr_name.txt "library" -> LibraryExt
        | [ x ] when String.equal x.attr_name.txt "inv" -> (
            match x.attr_payload with
            | PPat (pat, Some expr) -> (
                match (pat.ppat_desc, expr.pexp_desc) with
                | Ppat_tuple _, Pexp_tuple _ ->
                    failwith "inv extension: tuple error"
                    (* let ids = *)
                    (*   List.map (fun id -> id.L.x) @@ Pat.patten_to_typed_ids pat *)
                    (* in *)
                    (* if List.length es != List.length ids then *)
                    (*   failwith "inv extension: length error" *)
                    (* else *)
                    (*   let props = List.map Autov.prop_of_ocamlexpr es in *)
                    (*   Inv (List.combine ids props) *)
                | Ppat_var name, _ -> Inv (name.txt, Autov.lit_of_ocamlexpr expr)
                | _ -> _failatwith __FILE__ __LINE__ "unknown extension")
            | _ -> _failatwith __FILE__ __LINE__ "unknown extension")
        | [] -> NoExt
        | _ -> _failatwith __FILE__ __LINE__ "unknown extension"
      in
      let name =
        match (Pat.pattern_to_slang value_binding.pvb_pat).x with
        | L.Var name -> name
        | _ -> failwith "die"
      in
      (* let () = Printf.printf "name:<%b>%s\n" a name in *)
      let refinement = t_of_ocamlexpr value_binding.pvb_expr in
      Some ((a, name), refinement)
  | Pstr_primitive _ -> None
  | _ -> raise @@ failwith "translate not a function value"

let refinement_of_ocamlstruct t_of_ocamlexpr structures =
  List.filter_map (refinement_of_ocamlstruct_one t_of_ocamlexpr) structures

let layout_one_refinement f (name, r) = spf "⊢ %s : %s\n" name @@ f r

let layout_refinements f l =
  spf "%s\n" (List.split_by "\n" (layout_one_refinement f) l)

let layout_normals l =
  List.split_by "\n"
    (fun (name, ty) -> spf "val %s: %s" name @@ Type.layout ty)
    l
