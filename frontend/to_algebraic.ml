open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
module L = Syntax.LRaw
open Syntax.EquationRaw
open Sugar

let pprint_id id = spf "%s" id.L.x
(* (Nt.layout ty) *)

let rec pprint_eqterm = function
  | EqtRet id -> id.x
  | EqtDo { dolhs; effop; effargs; body } ->
      spf "%s <- %s (%s); %s" (pprint_id dolhs) (pprint_id effop)
        (List.split_by_comma pprint_id effargs)
        (pprint_eqterm body)

let pprint_equation = function
  | EqState (eta1, eta2) ->
      spf "%s ≃ %s" (pprint_eqterm eta1) (pprint_eqterm eta2)
  | EqObv (eta1, eta2) ->
      spf "%s ≃r %s" (pprint_eqterm eta1) (pprint_eqterm eta2)

let pprint_eqspace { domain; equationset } =
  spf "{%s}:{%s}"
    (List.split_by ";"
       (fun (k, v) -> spf "%s:%s" k (Nt.layout v))
       (StrMap.to_kv_list domain))
    (List.split_by ";" pprint_equation equationset)

let ids_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_ident id -> [ To_id.longid_to_id id ]
    | Pexp_tuple ids -> List.concat @@ List.map aux ids
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux expr

type parset =
  | PRetEvent of eqterm
  | PEqtDo of string L.typed * string L.typed list

let eqevent_of_ocamlexpr expr =
  let aux expr =
    match expr.pexp_desc with
    | Pexp_construct (op, Some e) -> (
        let op = To_id.longid_to_id op in
        let args = ids_of_ocamlexpr e in
        let open L in
        match (op, args) with
        | "Ret", [ v ] -> PRetEvent (EqtRet v #: None)
        | "Ret", _ -> _failatwith __FILE__ __LINE__ "die"
        | _, args ->
            let args = List.map (fun x -> x #: None) args in
            PEqtDo (op #: None, args))
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux expr

let eqterm_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ -> (
        match eqevent_of_ocamlexpr expr with
        | PRetEvent eqt -> eqt
        | _ -> _failatwith __FILE__ __LINE__ "die")
    | Pexp_let (_, [ vb ], body) -> (
        let dolhs =
          match To_pat.patten_to_typed_ids vb.pvb_pat with
          | [ id ] -> id
          | _ -> failwith "rty_of_ocamlexpr"
        in
        match eqevent_of_ocamlexpr vb.pvb_expr with
        | PEqtDo (effop, effargs) ->
            EqtDo { dolhs; effop; effargs; body = aux body }
        | _ -> _failatwith __FILE__ __LINE__ "die")
    | _ ->
        _failatwith __FILE__ __LINE__
          (spf "wrong refinement type: %s"
             (Pprintast.string_of_expression expr))
  in
  aux expr

let equation_of_ocamlexpr expr =
  let aux expr =
    match expr.pexp_desc with
    | Pexp_apply (func, args) -> (
        let f = To_expr.id_of_ocamlexpr func in
        let args = List.map snd args in
        match (f, args) with
        | "eq", [ e1; e2 ] ->
            EqState (eqterm_of_ocamlexpr e1, eqterm_of_ocamlexpr e2)
        | "eqr", [ e1; e2 ] ->
            EqObv (eqterm_of_ocamlexpr e1, eqterm_of_ocamlexpr e2)
        | _, _ -> _failatwith __FILE__ __LINE__ "die")
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux expr

let layout = pprint_eqspace
let layout_equation = pprint_equation
let layout_eqterm = pprint_eqterm
