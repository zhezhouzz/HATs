module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw.SRL
open Sugar
open Aux

let rec pprint_aux = function
  | EmptyA -> ("∅", true)
  | EpsilonA -> ("ϵ", true)
  | EventA se -> (To_se.pprint se, true)
  | LorA (a1, a2) ->
      (spf "%s%s%s" (p_pprint a1) psetting.sym_or (p_pprint a2), false)
  | SetMinusA (a1, a2) -> (spf "%s\\%s" (p_pprint a1) (p_pprint a2), false)
  | LandA (a1, a2) ->
      (spf "%s%s%s" (p_pprint a1) psetting.sym_and (p_pprint a2), false)
  | SeqA (a1, a2) -> (spf "%s;%s" (p_pprint a1) (p_pprint a2), false)
  | StarA AnyA -> (".*", false)
  | StarA a -> (spf "%s*" (p_pprint a), false)
  | AnyA -> (".", true)
  (* | ComplementA (EventA se) -> spf "%sᶜ" (pprint (EventA se)) *)
  | ComplementA a -> (spf "%sᶜ" (p_pprint a), false)

and p_pprint a =
  let str, is_p = pprint_aux a in
  if is_p then str else spf "(%s)" str

and pprint a = fst (pprint_aux a)

let layout = pprint

let of_ocamlexpr_aux expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_ident id ->
        let id = To_id.longid_to_id id in
        if String.equal "epsilonA" id then EpsilonA
        else if String.equal "emptyA" id then EmptyA
        else if String.equal "anyA" id then AnyA
        else
          _failatwith __FILE__ __LINE__
            (spf "the automata var (%s) are disallowed" id)
    | Pexp_apply (func, args) -> (
        let f = To_expr.id_of_ocamlexpr func in
        let args = List.map snd args in
        match (f, args) with
        | "starA", [ e1 ] -> StarA (aux e1)
        | "not", [ e1 ] -> ComplementA (aux e1)
        | "mu", _ ->
            _failatwith __FILE__ __LINE__
              "the recursive automata are disallowed"
        | "||", [ a; b ] -> LorA (aux a, aux b)
        | "-", [ a; b ] -> SetMinusA (aux a, aux b)
        | "&&", [ a; b ] -> LandA (aux a, aux b)
        | _, _ -> _failatwith __FILE__ __LINE__ @@ spf "unknown regular op %s" f
        )
    | Pexp_sequence (a, b) -> SeqA (aux a, aux b)
    | Pexp_construct _ -> EventA (To_se.of_ocamlexpr expr)
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux expr

let of_ocamlexpr expr =
  let rty = of_ocamlexpr_aux expr in
  let rty = Syntax.RtyRaw.SRL.normalize_name rty in
  (* let () = Printf.printf "ZZ: %s\n" (pprint_rty rty) in *)
  rty
