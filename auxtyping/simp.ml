open Language
module P = Rty.P
open Rty
(* open Sugar *)

let simp regex =
  let rec aux regex =
    match regex with
    | EpsilonA | AnyA | EmptyA | EventA _ -> regex
    | LorA (t1, t2) -> (
        match (aux t1, aux t2) with
        | EmptyA, _ -> t2
        | _, EmptyA -> t1
        | _, _ -> LorA (t1, t2))
    | SetMinusA (t1, t2) -> (
        match (aux t1, aux t2) with
        | EmptyA, _ -> EmptyA
        | _, EmptyA -> t1
        | _, _ -> SetMinusA (t1, t2))
    | LandA (t1, t2) -> (
        match (aux t1, aux t2) with
        | EmptyA, _ | _, EmptyA -> EmptyA
        | _, _ -> LandA (t1, t2))
    | SeqA (t1, t2) -> (
        match (aux t1, aux t2) with
        | EmptyA, _ | _, EmptyA -> EmptyA
        | EpsilonA, regex2 -> regex2
        | regex1, EpsilonA -> regex1
        | EventA (GuardEvent phi1), EventA (GuardEvent phi2) ->
            EventA (GuardEvent (P.smart_and [ phi1; phi2 ]))
        | EventA (GuardEvent phi1), SeqA (EventA (GuardEvent phi2), r) ->
            aux (SeqA (EventA (GuardEvent (P.smart_and [ phi1; phi2 ])), r))
        | regex1, regex2 -> SeqA (regex1, regex2))
    | StarA t -> StarA (aux t)
    | ComplementA t -> (
        match aux t with ComplementA t -> t | t -> ComplementA t)
  in
  aux regex
