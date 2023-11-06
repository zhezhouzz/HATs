open Language
module Typectx = NTypectx

(* open Zzdatatype.Datatype *)
(* open Sugar *)
(* open Qualifiercheck *)
open RtyRaw.SRL
(* open Aux *)

let rec check opctx ctx (srl : regex) : regex =
  let () =
    Env.show_log "ntyping" @@ fun _ ->
    Printf.printf ">>>>>>>>>SRL Check %s\n" (To_srl.layout srl)
  in
  match srl with
  | EpsilonA | AnyA | EmptyA -> srl
  | EventA se -> EventA (Secheck.check opctx ctx se)
  | LorA (t1, t2) -> LorA (check opctx ctx t1, check opctx ctx t2)
  | SetMinusA (t1, t2) -> SetMinusA (check opctx ctx t1, check opctx ctx t2)
  | LandA (t1, t2) -> LandA (check opctx ctx t1, check opctx ctx t2)
  | SeqA (t1, t2) -> SeqA (check opctx ctx t1, check opctx ctx t2)
  | StarA t -> StarA (check opctx ctx t)
  | ComplementA t -> ComplementA (check opctx ctx t)
