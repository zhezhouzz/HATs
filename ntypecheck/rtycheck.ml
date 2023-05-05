open Language
module Typectx = NTypectx
open Zzdatatype.Datatype
open Sugar
open Qualifiercheck
open RtyRaw
(* open Aux *)

let cty_check ctx { v; phi } =
  let ctx' = Typectx.new_to_rights ctx [ v ] in
  let phi = type_check_qualifier ctx' phi in
  { v; phi }

let rec pty_check ctx (rty : pty) : pty =
  let rec aux ctx rty =
    match rty with
    | BasePty { ou; cty } -> BasePty { ou; cty = cty_check ctx cty }
    | TuplePty ptys -> TuplePty (List.map (aux ctx) ptys)
    | ArrPty { rarg; retrty } ->
        let rarg = { px = rarg.px; pty = aux ctx rarg.pty } in
        let ctx' =
          match rarg.px with
          | None -> ctx
          | Some x -> Typectx.new_to_right ctx Nt.(x #: (erase_pty rarg.pty))
        in
        let retrty = rty_check ctx' retrty in
        ArrPty { rarg; retrty }
  in
  aux ctx rty

and sevent_check ctx retbty sevent =
  match sevent with
  | RetEvent pty ->
      let pty = pty_check ctx pty in
      let _ = _check_equality __FILE__ __LINE__ Nt.eq retbty (erase_pty pty) in
      RetEvent pty
  | EffEvent { op; vs; phi } ->
      let opty = Aux.infer_op ctx (Op.EffOp op) in
      let argsty, _ = Nt.destruct_arr_tp opty in
      let vs =
        List.map
          Nt.(
            fun ({ x; ty }, ty') ->
              let ty = _check_equality __FILE__ __LINE__ eq ty ty' in
              { x; ty })
          (_safe_combine __FILE__ __LINE__ vs argsty)
      in
      let ctx' = Typectx.new_to_rights ctx vs in
      let phi = type_check_qualifier ctx' phi in
      EffEvent { op; vs; phi }

and regex_check ctx retbty (regex : regex) : regex =
  let rec aux regex =
    match regex with
    | VarA x -> VarA x
    | EpsilonA -> EpsilonA
    | EventA se -> EventA (sevent_check ctx retbty se)
    | LorA (t1, t2) -> LorA (aux t1, aux t2)
    | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
    | StarA t -> StarA (aux t)
    | ExistsA { localx = { cx; cty }; regex } ->
        let cty = cty_check ctx cty in
        let ctx' = Typectx.new_to_right ctx Nt.(cx #: (erase_cty cty)) in
        ExistsA { localx = { cx; cty }; regex = regex_check ctx' retbty regex }
    | RecA { mux; muA; index; regex } ->
        let indty = Nt.Ty_int in
        let index = (type_check_lit ctx (index, indty)).x in
        let ctx' = Typectx.new_to_right ctx Nt.(mux #: indty) in
        RecA { mux; muA; index; regex = regex_check ctx' retbty regex }
  in
  aux regex

and rty_check ctx (rty : t) : t =
  match rty with
  | Pty pty -> Pty (pty_check ctx pty)
  | Regty regex -> Regty Nt.((regex_check ctx regex.ty) #-> regex)
