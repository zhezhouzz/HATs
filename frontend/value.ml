open Ast
module V = Value
open Ocaml_parser
open Parsetree
open Sugar
open Zzdatatype.Datatype

let longident_to_string ld =
  match Longident.flatten ld with
  | [] -> failwith "die"
  | [ t ] -> t
  | _ -> failwith "un-imp"

let string_to_loc str = Location.mknoloc @@ Longident.Lident str

let dummy_expr pexp_desc =
  {
    pexp_desc;
    pexp_loc = Location.none;
    pexp_loc_stack = [];
    pexp_attributes = [];
  }

(* TODO: exception *)
let string_to_value = function
  | "true" -> V.B true
  | "false" -> V.B false
  | "Leaf" -> V.IT Tree.Leaf
  | "()" -> V.U
  | "Empty" -> V.U
  | "[]" -> V.IL []
  | x -> failwith (spf "do not support literal: %s" x)

let rec expr_to_value e =
  let mk_exn () =
    failwith
      (spf "do not support complicate literal: %s"
         (Pprintast.string_of_expression e))
  in
  match e.pexp_desc with
  | Pexp_tuple es -> V.Tu (List.map expr_to_value es)
  | Pexp_construct (id, e) -> (
      let name = longident_to_string id.txt in
      match e with
      | None -> string_to_value name
      | Some e -> (
          match (name, expr_to_value e) with
          | "::", V.Tu [ V.I hd; V.IL tl ] -> V.IL (hd :: tl)
          | "Node", V.Tu [ V.I x; V.IT a; V.IT b ] -> V.IT (Tree.Node (x, a, b))
          | "NodeS", V.Tu [ V.I x ] ->
              V.IT (Tree.Node (x, Tree.Leaf, Tree.Leaf))
          | _, _ -> mk_exn ()))
  | Pexp_constant (Pconst_integer (istr, None)) -> V.I (int_of_string istr)
  | _ -> mk_exn ()

let value_to_expr v =
  let name_to_expr name e =
    dummy_expr (Pexp_construct (string_to_loc name, e))
  in
  let rec aux = function
    | V.U -> name_to_expr "()" None
    | V.B true -> name_to_expr "true" None
    | V.B false -> name_to_expr "false" None
    | V.I i ->
        dummy_expr (Pexp_constant (Pconst_integer (string_of_int i, None)))
    | V.IL [] -> name_to_expr "[]" None
    | V.IL (h :: t) -> name_to_expr "::" (Some (aux V.(Tu [ I h; IL t ])))
    | V.IT Tree.Leaf -> name_to_expr "Leaf" None
    | V.IT (Tree.Node (x, a, b)) ->
        name_to_expr "Node" (Some (aux V.(Tu [ I x; IT a; IT b ])))
    | V.Tu l -> dummy_expr (Pexp_tuple (List.map aux l))
    | _ -> failwith "un-imp"
  in
  aux v

let layout v = Pprintast.string_of_expression @@ value_to_expr v
let layout_l ts = List.split_by_comma layout ts
