open Syntax
module R = LRaw
open L
open Sugar

let force file line R.{ x; ty } =
  match ty with
  | None -> _failatwith file line "force_typed"
  | Some ty -> Nt.(x #: ty)

let besome { x; ty } = R.(x #: (Some ty))
