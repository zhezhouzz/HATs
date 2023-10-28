open Language
module Typectx = NTypectx

(* open Zzdatatype.Datatype *)
open Sugar

(* open Qualifiercheck *)
open RtyRaw
(* open Aux *)

let rec hty_check opctx ctx (hty : hty) : hty =
  match hty with
  | Rty rty -> Rty (rty_check opctx ctx rty)
  | Htriple { pre; resrty; post } ->
      let pre = Srlcheck.check opctx ctx pre in
      let post = Srlcheck.check opctx ctx post in
      let resrty = rty_check opctx ctx resrty in
      Htriple { pre; resrty; post }
  | Inter (h1, h2) ->
      let h1 = hty_check opctx ctx h1 in
      let h2 = hty_check opctx ctx h2 in
      let _ =
        _assert __FILE__ __LINE__ "syntax error: intersection type"
          (Nt.eq (erase_hty h1) (erase_hty h2))
      in
      Inter (h1, h2)

and arr_check opctx ctx (arr : arr) : arr * string Nt.typed option =
  match arr with
  | NormalArr { rx; rty } ->
      let rty = rty_check opctx ctx rty in
      (NormalArr { rx; rty }, Some Nt.{ x = rx; ty = erase_rty rty })
  | GhostArr x -> (GhostArr x, Some x)
  | ArrArr rty -> (ArrArr (rty_check opctx ctx rty), None)

and rty_check opctx ctx (hty : rty) : rty =
  (* let () = Printf.printf "hty: %s\n" @@ StructureRaw.layout_rty hty in *)
  match hty with
  | BaseRty { cty } -> BaseRty { cty = Ctycheck.check opctx ctx cty }
  | ArrRty { arr; rethty } ->
      let arr, binding = arr_check opctx ctx arr in
      let ctx' =
        match binding with
        | None -> ctx
        | Some binding -> Typectx.new_to_right ctx binding
      in
      let rethty = hty_check opctx ctx' rethty in
      ArrRty { arr; rethty }
