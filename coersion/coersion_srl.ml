open Syntax
module Raw = RtyRaw
open Rty
module SE = Coersion_se

let force regex =
  let rec aux regex =
    match regex with
    | Raw.EmptyA -> EmptyA
    | Raw.AnyA -> AnyA
    | Raw.EpsilonA -> EpsilonA
    | Raw.EventA se -> EventA (SE.force se)
    | Raw.LorA (t1, t2) -> LorA (aux t1, aux t2)
    | Raw.SetMinusA (t1, t2) -> SetMinusA (aux t1, aux t2)
    | Raw.LandA (t1, t2) -> LandA (aux t1, aux t2)
    | Raw.SeqA (t1, t2) -> SeqA (aux t1, aux t2)
    | Raw.StarA t -> StarA (aux t)
    | Raw.ComplementA t -> ComplementA (aux t)
  in
  aux regex

let besome regex =
  let rec aux regex =
    match regex with
    | EmptyA -> Raw.EmptyA
    | AnyA -> Raw.AnyA
    | EpsilonA -> Raw.EpsilonA
    | EventA se -> Raw.EventA (SE.besome se)
    | LorA (t1, t2) -> Raw.LorA (aux t1, aux t2)
    | SetMinusA (t1, t2) -> Raw.SetMinusA (aux t1, aux t2)
    | LandA (t1, t2) -> Raw.LandA (aux t1, aux t2)
    | SeqA (t1, t2) -> Raw.SeqA (aux t1, aux t2)
    | StarA t -> Raw.StarA (aux t)
    | ComplementA t -> Raw.ComplementA (aux t)
  in
  aux regex
