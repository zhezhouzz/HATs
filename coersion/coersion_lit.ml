open Syntax
module R = LRaw
open L
module A = Coersion_aux

let rec force_typed lit = A.force __FILE__ __LINE__ R.(force #-> lit)

and force lit =
  match lit with
  | R.AC c -> AC c
  | R.AVar x -> AVar x
  | R.ATu l -> ATu (List.map force_typed l)
  | R.AProj (a, n) -> AProj (force_typed a, n)
  | R.AAppOp (f, args) ->
      AAppOp (A.force __FILE__ __LINE__ f, List.map force_typed args)

let rec besome_typed lit = A.besome besome #-> lit

and besome lit =
  match lit with
  | AC c -> R.AC c
  | AVar x -> R.AVar x
  | ATu l -> R.ATu (List.map besome_typed l)
  | AProj (a, n) -> R.AProj (besome_typed a, n)
  | AAppOp (f, args) -> R.AAppOp (A.besome f, List.map besome_typed args)
