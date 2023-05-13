open Language
open Rty
open Sugar

type dep_quantifer = SigmaTy of string ctyped | PiTy of string ctyped

let dep_quantifer_flip = function SigmaTy x -> PiTy x | PiTy x -> SigmaTy x
let dep_quantifer_get_id = function SigmaTy x -> x.cx | PiTy x -> x.cx

let ptyped_to_dep_quantifer = function
  | { px; pty = BasePty { ou = Under; cty } } -> SigmaTy { cx = px; cty }
  | _ -> _failatwith __FILE__ __LINE__ "die"

let typed_to_dep_quantifer_opt = function
  | { x; ty = Pty pty } -> Some (ptyped_to_dep_quantifer { px = x; pty })
  | _ -> None

let close_to_prop (x : dep_quantifer) phi =
  match x with
  | SigmaTy x ->
      let x, phix = cty_typed_to_prop x in
      smart_sigma (x, phix) phi
  | PiTy x ->
      let x, phix = cty_typed_to_prop x in
      smart_pi (x, phix) phi

let dep_quantifer_to_typed dq =
  match dq with
  | PiTy _ -> _failatwith __FILE__ __LINE__ "die"
  | SigmaTy { cx; cty } -> cx #: (Pty (BasePty { ou = Under; cty }))
