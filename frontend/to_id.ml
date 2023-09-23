open Ocaml5_parser

(* open Parsetree *)
open Sugar
(* open Syntax.NTyped *)

let longid_to_id c =
  match Longident.flatten c.Location.txt with
  | [] -> _failatwith __FILE__ __LINE__ "die"
  | [ c ] -> c
  | _ -> _failatwith __FILE__ __LINE__ "un-imp"

let id_to_longid x =
  match Longident.unflatten [ x ] with
  | Some x -> Location.mknoloc x
  | None -> _failatwith __FILE__ __LINE__ "die"
