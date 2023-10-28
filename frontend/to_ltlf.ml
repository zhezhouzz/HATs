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
    | EventL se -> To_se.layout se
    | LastL -> "LAST"
    | FinalL a -> spf "♢%s" (force_paren @@ aux a)
    | GlobalL a -> spf "☐%s" (force_paren @@ aux a)
    | NegL a -> spf "%s%s" psetting.sym_not (force_paren @@ aux a)
    | LandL (a1, a2) ->
        spf "%s%s%s"
          (force_paren @@ aux a1)
          psetting.sym_and
          (force_paren @@ aux a2)
    | LorL (a1, a2) ->
        spf "%s%s%s"
          (force_paren @@ aux a1)
          psetting.sym_or
          (force_paren @@ aux a2)
    | SeqL (a1, a2) ->
        spf "%s;%s" (force_paren @@ aux a1) (force_paren @@ aux a2)
    | NextL a -> spf "◯%s" (force_paren @@ aux a)
    | UntilL (a1, a2) ->
        spf "%s𝒰%s" (force_paren @@ aux a1) (force_paren @@ aux a2)
  in
  aux ltlf

let layout = pprint

let of_ocamlexpr_aux expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_ident id ->
        let id = To_id.longid_to_id id in
        if String.equal "lastL" id then LastL
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
        | "not", [ e1 ] -> NegL (aux e1)
        | "||", [ a; b ] ->
            (* let () = Printf.printf "11\n" in *)
            LorL (aux a, aux b)
        | "&&", [ a; b ] ->
            (* let () = Printf.printf "2\n" in *)
            LandL (aux a, aux b)
        | _, _ -> _failatwith __FILE__ __LINE__ @@ spf "unknown regular op %s" f
        )
    | Pexp_sequence (a, b) -> SeqL (aux a, aux b)
    | Pexp_construct _ -> EventL (To_se.of_ocamlexpr expr)
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux expr

let of_ocamlexpr expr =
  let ltlf = of_ocamlexpr_aux expr in
  let ltlf = ensugar ltlf in
  ltlf
