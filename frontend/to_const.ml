module C = Syntax.Const
open Ocaml5_parser
open Parsetree
open Sugar
open Zzdatatype.Datatype

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
  | x -> failwith (spf "do not support literal: %s" x)

let rec expr_to_value e =
  let mk_exn () =
    failwith
      (spf "do not support complicate literal: %s"
         (Pprintast.string_of_expression e))
  in
  match e.pexp_desc with
  | Pexp_tuple es -> C.Tu (List.map expr_to_value es)
  | Pexp_construct (id, e) -> (
      let name = To_id.longid_to_id id in
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
    dummy_expr (Pexp_construct (To_id.id_to_longid name, e))
  in
  let rec aux v =
    match v with
    | C.U | C.B _ -> name_to_expr (C.layout v) None
    | C.Dt (op, vs) ->
        dummy_expr
          (Pexp_construct
             ( To_id.id_to_longid (To_op.op_to_string (Op.DtOp op)),
               Some (aux (C.Tu vs)) ))
    | C.I i ->
        dummy_expr (Pexp_constant (Pconst_integer (string_of_int i, None)))
    | C.Tu l -> dummy_expr (Pexp_tuple (List.map aux l))
  in
  aux v

let layout v = Pprintast.string_of_expression @@ value_to_expr v
let layout_l ts = List.split_by_comma layout ts
