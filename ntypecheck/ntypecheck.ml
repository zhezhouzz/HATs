open Language
module Typectx = NTypectx
open Sugar
open StructureRaw
open Coersion
open Rtycheck

let opt_to_typed_rty ctx rty : Rty.t = force_rty (rty_check ctx rty)
let opt_to_typed_pty ctx rty : Rty.pty = force_pty (pty_check ctx rty)
let opt_to_typed_cty ctx cty : Rty.cty = force_cty (cty_check ctx cty)

open Ttypecheck

let opt_to_typed_term ctx body ty = force_typed_term @@ type_check ctx body ty

let struc_infer_one ctx x if_rec body =
  let rec get_fty e =
    match e.x with
    | Lam { lamarg; lambody } ->
        Sugar.(
          let* bty = get_fty lambody in
          let* aty = lamarg.ty in
          Some (Nt.Ty_arrow (aty, bty)))
    | _ -> e.ty
  in
  let res =
    match (if_rec, get_fty body) with
    | true, None ->
        _failatwith __FILE__ __LINE__ "require the return type of the function"
    | false, ty -> type_check ctx body ty
    | true, Some ty ->
        type_check Typectx.(new_to_right ctx { x; ty }) body (Some ty)
  in
  res

let opt_to_typed_structure ctx qctx l =
  let () = NTypectx.pretty_print_lines ctx in
  let l = map_imps (struc_infer_one ctx) l in
  let l = map_rtys (rty_check qctx) l in
  force_structure l
