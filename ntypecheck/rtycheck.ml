open Language
module Typectx = NTypectx
open Zzdatatype.Datatype
open Sugar
open Qualifiercheck
open RtyRaw
(* open Aux *)

let cty_check opctx ctx { v; phi } =
  let ctx' = Typectx.new_to_rights ctx [ v ] in
  let phi = type_check_qualifier opctx ctx' phi in
  { v; phi }

let rec rty_check opctx ctx (rty : rty) : rty =
  match rty with
  | Pty pty -> Pty (pty_check opctx ctx pty)
  | Regty regex -> Regty Nt.((regex_check opctx ctx regex.ty) #-> regex)

and pty_check opctx ctx (rty : pty) : pty =
  let rec aux ctx rty =
    match rty with
    | BasePty { cty } -> BasePty { cty = cty_check opctx ctx cty }
    | TuplePty ptys -> TuplePty (List.map (aux ctx) ptys)
    | ArrPty { rarg; retrty } ->
        let rarg = { px = rarg.px; pty = aux ctx rarg.pty } in
        let () =
          match rarg.px with
          | None ->
              _assert __FILE__ __LINE__
                (spf "syntax error: argument type %s" (To_rty.layout_pty rty))
              @@ (is_arr_pty rarg.pty || is_base_pty rarg.pty)
          | Some _ ->
              _assert __FILE__ __LINE__ "syntax error: argument type"
              @@ is_base_pty rarg.pty
        in
        let ctx' =
          match rarg.px with
          | None -> ctx
          | Some x -> Typectx.new_to_right ctx Nt.(x #: (erase_pty rarg.pty))
        in
        let retrty = rty_check opctx ctx' retrty in
        ArrPty { rarg; retrty }
  in
  aux ctx rty

and sevent_check opctx ctx retbty sevent =
  match sevent with
  | GuardEvent phi ->
      let phi = type_check_qualifier opctx ctx phi in
      GuardEvent phi
  | RetEvent pty ->
      let pty = pty_check opctx ctx pty in
      let _ = _check_equality __FILE__ __LINE__ Nt.eq retbty (erase_pty pty) in
      RetEvent pty
  | EffEvent { op; vs; phi } ->
      let opty = Aux.infer_op opctx (Op.EffOp op) in
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
      let phi = type_check_qualifier opctx ctx' phi in
      EffEvent { op; vs; phi }

and regex_check opctx ctx retbty (regex : regex) : regex =
  match regex with
  | EpsilonA -> EpsilonA
  | EventA se -> EventA (sevent_check opctx ctx retbty se)
  | LorA (t1, t2) ->
      LorA (regex_check opctx ctx retbty t1, regex_check opctx ctx retbty t2)
  | LandA (t1, t2) ->
      LandA (regex_check opctx ctx retbty t1, regex_check opctx ctx retbty t2)
  | SeqA (t1, t2) ->
      SeqA (regex_check opctx ctx retbty t1, regex_check opctx ctx retbty t2)
  | StarA t -> StarA (regex_check opctx ctx retbty t)
