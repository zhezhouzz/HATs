module C = Ast.Const
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

let string_to_value = function
  | "true" -> C.B true
  | "false" -> C.B false
  | "()" -> C.U
  (* | "Err" -> C.Err *)
  | x -> failwith (spf "do not support literal: %s" x)

let rec expr_to_value e =
  let mk_exn () =
    failwith
      (spf "do not support complicate literal: %s"
         (Pprintast.string_of_expression e))
  in
  match e.pexp_desc with
  | Pexp_tuple _ ->
      _failatwith __FILE__ __LINE__ "not support tuple constants"
      (* C.Tu (List.map expr_to_value es) *)
  | Pexp_construct (id, e) -> (
      let name = longident_to_string id.txt in
      match e with
      | None -> string_to_value name
      | Some e -> (
          match (name, expr_to_value e) with
          (* | "::", C.Tu [ C.I hd; C.IL tl ] -> C.IL (hd :: tl) *)
          | _, _ -> mk_exn ()))
  | Pexp_constant (Pconst_integer (istr, None)) -> C.I (int_of_string istr)
  | _ -> mk_exn ()

let value_to_expr v =
  let name_to_expr name e =
    dummy_expr (Pexp_construct (string_to_loc name, e))
  in
  let aux v =
    match v with
    | C.U | C.B _ | C.Prim _ -> name_to_expr (C.layout v) None
    | C.I i ->
        dummy_expr (Pexp_constant (Pconst_integer (string_of_int i, None)))
    (* | C.IL [] -> name_to_expr "[]" None *)
    (* | C.IL (h :: t) -> name_to_expr "::" (Some (aux C.(Tu [ I h; IL t ]))) *)
    (* | C.Tu l -> dummy_expr (Pexp_tuple (List.map aux l)) *)
    (* | _ -> failwith "un-imp" *)
  in
  aux v

let layout v = Pprintast.string_of_expression @@ value_to_expr v
let layout_l ts = List.split_by_comma layout ts
