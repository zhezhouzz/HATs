module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw.LTLf
open Sugar
open Aux

(* let pprint_final_opt ltlf = *)
(*   match to_final_opt ltlf with *)
(*   | Some a -> Result.Error (spf "♢%s" (force_paren @@ pprint a)) *)
(*   | None -> Result.Ok ltlf *)

(* let pprint_global_opt ltlf = *)
(*   match to_global_opt ltlf with *)
(*   | Some a -> Result.Error (spf "☐%s" (force_paren @@ pprint a)) *)
(*   | None -> Result.Ok ltlf *)

(* let pprint_last_opt ltlf = *)
(*   match ltlf with *)
(*   | LandL (a, b) -> *)
(*     if is_last a *)
(*     then Result.Error (spf "LAST%s%s" *)
(*                          psetting.sym_and *)
(*                          (force_paren @@ pprint a)) *)
(*     else Result.Ok ltlf *)
(*   | _ -> Result.Ok ltlf *)

let pprint ltlf =
  let rec aux ltlf =
    match ltlf with
    | EventL se -> (To_se.layout se, true)
    | LastL -> ("LAST", true)
    | FinalL a -> (spf "♢%s" (p_pprint a), true)
    | GlobalL a -> (spf "☐%s" (p_pprint a), true)
    | NegL a -> (spf "%s%s" psetting.sym_not (p_pprint a), true)
    | LandL (a1, a2) ->
        (spf "%s%s%s" (p_pprint a1) psetting.sym_and (p_pprint a2), false)
    | LorL (a1, a2) ->
        (spf "%s%s%s" (p_pprint a1) psetting.sym_or (p_pprint a2), false)
    | SeqL (a1, a2) -> (spf "%s;%s" (p_pprint a1) (p_pprint a2), false)
    | NextL a -> (spf "◯%s" (p_pprint a), true)
    | UntilL (a1, a2) -> (spf "%s𝒰 %s" (p_pprint a1) (p_pprint a2), false)
    | SFAPred { name; args } ->
        (spf "%s(%s)" name (List.split_by_comma To_lit.layout args), true)
  and p_pprint a =
    let str, is_p = aux a in
    if is_p then str else spf "(%s)" str
  in
  fst @@ aux ltlf

let layout = pprint

let of_ocamlexpr_aux expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_ident id ->
        let id = To_id.longid_to_id id in
        if String.equal "lastL" id then LastL
        else if String.equal "rI" id then SFAPred { name = id; args = [] }
        else
          _failatwith __FILE__ __LINE__
            (spf "the automata var (%s) are disallowed" id)
    | Pexp_apply (func, args) -> (
        let f = To_expr.id_of_ocamlexpr func in
        let args = List.map snd args in
        match (f, args) with
        | "_F", [ e1 ] -> FinalL (aux e1)
        | "_G", [ e1 ] -> GlobalL (aux e1)
        | "_X", [ e1 ] -> NextL (aux e1)
        | "_U", [ a; b ] -> UntilL (aux a, aux b)
        | "implies", [ a; b ] -> LorL (NegL (aux a), aux b)
        | "#==>", [ a; b ] -> LorL (NegL (aux a), aux b)
        | "iff", [ a; b ] ->
            let a, b = map2 aux (a, b) in
            LandL (LorL (NegL a, b), LorL (NegL b, a))
        | "not", [ e1 ] -> NegL (aux e1)
        | "||", [ a; b ] ->
            (* let () = Printf.printf "11\n" in *)
            LorL (aux a, aux b)
        | "&&", [ a; b ] ->
            (* let () = Printf.printf "2\n" in *)
            LandL (aux a, aux b)
        | name, args ->
            let args = List.map To_lit.lit_of_ocamlexpr args in
            SFAPred { name; args }
        (* _failatwith __FILE__ __LINE__ @@ spf "unknown regular op %s" f *))
    | Pexp_sequence (a, b) -> SeqL (aux a, aux b)
    | Pexp_construct _ -> EventL (To_se.of_ocamlexpr expr)
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux expr

let of_ocamlexpr expr =
  let ltlf = of_ocamlexpr_aux expr in
  let ltlf = ensugar ltlf in
  ltlf
