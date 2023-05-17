open Language
module P = Rty.P
open Rty

(* open Sugar *)

let rec concat r = function
  | Pty pty -> concat r (pty_to_ret_rty pty)
  | Regty Nt.{ x; ty } -> Regty Nt.{ x = SeqA (r, x); ty }
