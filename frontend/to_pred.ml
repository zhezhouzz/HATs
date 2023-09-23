module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module NTyped = Normalty.Ntyped
module TL = Syntax.OptTypedTermlang
open Syntax.QualifierRaw
open Sugar

(* pred is untyped *)
let pred_to_ocamlexpr_desc expr =
  let aux e =
    match e with
    | Lit lit -> To_lit.lit_to_ocamlexpr_desc lit #: None
    | MethodPred (mp, args) ->
        Pexp_apply
          ( To_expr.id_to_ocamlexpr mp,
            List.map
              (fun x -> (Asttypes.Nolabel, To_lit.lit_to_ocamlexpr x))
              args )
  in
  aux expr

let pred_to_ocamlexpr expr =
  To_expr.desc_to_ocamlexpr @@ pred_to_ocamlexpr_desc expr

let layout_pred pred = Pprintast.string_of_expression @@ pred_to_ocamlexpr pred

let term_to_pred e =
  match e.x with
  | TL.App (func, args) -> (
      match TL.to_var_opt func with
      | Some mp -> MethodPred (mp, List.map To_lit.term_to_lit args)
      | None -> _failatwith __FILE__ __LINE__ "die")
  | _ -> Lit (To_lit.term_to_lit e).x

let pred_of_ocamlexpr e = term_to_pred (To_expr.expr_of_ocamlexpr e)
