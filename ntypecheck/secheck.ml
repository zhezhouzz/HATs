open Language
module Typectx = NTypectx
open Zzdatatype.Datatype
open Sugar
open Qualifiercheck
open RtyRaw.SE
(* open Aux *)

let check opctx ctx sevent =
  match sevent with
  | GuardEvent phi ->
      let phi = type_check_qualifier opctx ctx phi in
      GuardEvent phi
  | EffEvent { op; vs; v; phi } ->
      (* let () = Printf.printf "sevent: %s\n" (To_hty.layout_sevent sevent) in *)
      (* let () = *)
      (*   Printf.printf "vs: %s\n" (List.split_by_comma (fun x -> x.Nt.x) vs) *)
      (* in *)
      let orty = Aux.infer_op opctx (Op.EffOp op) in
      let argsty, retnty = Nt.destruct_arr_tp orty in
      let vs =
        List.map
          (fun ({ x; ty }, ty') ->
            (* let () = *)
            (*   Printf.printf "%s: %s ?= %s\n" op (layout ty) (Nt.layout ty') *)
            (* in *)
            let ty = _type_unify __FILE__ __LINE__ ty (Some ty') in
            { x; ty })
          (_safe_combine __FILE__ __LINE__ vs argsty)
      in
      let retnty = _type_unify __FILE__ __LINE__ v.ty (Some retnty) in
      let v = { x = v.x; ty = retnty } in
      let bindings =
        List.map (Coersion.Aux.force __FILE__ __LINE__) (v :: vs)
      in
      let ctx' = Typectx.new_to_rights ctx bindings in
      let phi = type_check_qualifier opctx ctx' phi in
      EffEvent { op; vs; v; phi }
