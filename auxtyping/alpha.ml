open Language
module P = Rty.P
open Rty

(* open Sugar *)
module NCtx = NTypectx

type tmp_under_ctx = NCtx.ctx

let add_localx_into_ctx ctx localx =
  let open P in
  let localx = Rename.unique #-> localx in
  (NCtx.new_to_right ctx localx, localx)

let get_localxs regex =
  let rec aux regex =
    match regex with
    | EpsilonA | EventA _ -> []
    | SigmaA { localx; _ } -> [ localx ]
    | LorA (t1, t2) -> aux t1 @ aux t2
    | LandA (t1, t2) -> aux t1 @ aux t2
    | SeqA (t1, t2) -> aux t1 @ aux t2
    | StarA t -> aux t
  in
  aux regex

open Zzdatatype.Datatype

let choose_need ctx vs =
  let open P in
  List.map
    (fun x -> List.find "choose_need" (fun y -> String.equal y.x x) ctx)
    vs

let to_rctx_ Nt.{ x; ty } =
  let pty = mk_top_pty ty in
  x #: (Pty pty)

let to_rctx ctx = List.map to_rctx_ ctx
let init regex = get_localxs regex

let alpha regex =
  let rec aux ctx regex =
    match regex with
    | EventA _ | EpsilonA -> (ctx, regex)
    | LorA (t1, t2) ->
        let ctx, r1 = aux ctx t1 in
        let ctx, r2 = aux ctx t2 in
        (ctx, LorA (r1, r2))
    | LandA (t1, t2) ->
        let ctx, r1 = aux ctx t1 in
        let ctx, r2 = aux ctx t2 in
        (ctx, LandA (r1, r2))
    | SeqA (t1, t2) ->
        let ctx, r1 = aux ctx t1 in
        let ctx, r2 = aux ctx t2 in
        (ctx, SeqA (r1, r2))
    | SigmaA { localx; xA; body } ->
        let ctx, xA = aux ctx xA in
        let ctx, localx' = add_localx_into_ctx ctx localx in
        let body = subst_regex_id (localx.Nt.x, localx'.Nt.x) body in
        let ctx, body = aux ctx body in
        (ctx, SigmaA { localx = localx'; xA; body })
    | StarA t ->
        let ctx, r = aux ctx t in
        (ctx, StarA r)
  in
  aux regex

let to_top_typed_regex regex =
  let rec aux topl regex =
    match regex with
    | EpsilonA | EventA _ -> (topl, regex)
    | SigmaA { localx; body; _ } -> aux (topl @ [ localx ]) body
    | LorA (t1, t2) ->
        let topl, r1 = aux topl t1 in
        let topl, r2 = aux topl t2 in
        (topl, LorA (r1, r2))
    | LandA (t1, t2) ->
        let topl, r1 = aux topl t1 in
        let topl, r2 = aux topl t2 in
        (topl, LandA (r1, r2))
    | SeqA (t1, t2) ->
        let topl, r1 = aux topl t1 in
        let topl, r2 = aux topl t2 in
        (topl, SeqA (r1, r2))
    | StarA t ->
        let topl, r = aux topl t in
        (topl, StarA r)
  in
  aux [] regex
