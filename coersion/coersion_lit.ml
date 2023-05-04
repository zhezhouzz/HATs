open Syntax
module R = LRaw
open L
open Coersion_aux

let rec force_typed_lit lit = force __FILE__ __LINE__ R.(force_lit #-> lit)

and force_lit lit =
  match lit with
  | R.AC c -> AC c
  | R.AVar x -> AVar x
  | R.ATu l -> ATu (List.map force_typed_lit l)
  | R.AProj (a, n) -> AProj (force_typed_lit a, n)
  | R.AAppOp (f, args) ->
      AAppOp (force __FILE__ __LINE__ f, List.map force_typed_lit args)

let rec besome_typed_lit lit = besome besome_lit #-> lit

and besome_lit lit =
  match lit with
  | AC c -> R.AC c
  | AVar x -> R.AVar x
  | ATu l -> R.ATu (List.map besome_typed_lit l)
  | AProj (a, n) -> R.AProj (besome_typed_lit a, n)
  | AAppOp (f, args) -> R.AAppOp (besome f, List.map besome_typed_lit args)
