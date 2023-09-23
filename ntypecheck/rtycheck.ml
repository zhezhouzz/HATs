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
  | Regty { nty; prereg; postreg } ->
      let prereg = regex_check opctx ctx None prereg in
      let postreg = regex_check opctx ctx (Some nty) postreg in
      Regty { nty; prereg; postreg }

and pty_check opctx ctx (rty : pty) : pty =
  (* let () = Printf.printf "rty: %s\n" @@ StructureRaw.layout_pty rty in *)
  let rec aux ctx rty =
    match rty with
    | BasePty { cty } -> BasePty { cty = cty_check opctx ctx cty }
    | TuplePty ptys -> TuplePty (List.map (aux ctx) ptys)
    | ArrPty { arr_kind; rarg; retrty } ->
        let pty = aux ctx rarg.pty in
        let rarg =
          { px = rarg.px; pty }
          (* if is_base_pty pty then { px = rarg.px; pty } else { px = None; pty } *)
        in
        let () =
          match rarg.px with
          | None ->
              _assert __FILE__ __LINE__
                (spf "syntax error: argument type %s" (To_rty.layout_pty rty))
              @@ (is_arr_pty rarg.pty || is_base_pty rarg.pty)
          | Some _ -> ()
          (* _assert __FILE__ __LINE__ "syntax error: argument type" *)
          (* @@ is_base_pty rarg.pty *)
        in
        let opctx', ctx' =
          match rarg.px with
          | None -> (opctx, ctx)
          | Some x -> (
              let nty = erase_pty rarg.pty in
              match arr_kind with
              (* | PiArr -> (opctx, Typectx.new_to_right ctx Nt.(x #: nty)) *)
              | SigamArr when not @@ Nt.is_basic_tp nty ->
                  ( NOpTypectx.new_to_right opctx Nt.((Op.BuiltinOp x) #: nty),
                    ctx )
              | _ -> (opctx, Typectx.new_to_right ctx Nt.(x #: nty)))
        in
        let retrty = rty_check opctx' ctx' retrty in
        ArrPty { arr_kind; rarg; retrty }
  in
  aux ctx rty

and sevent_check opctx ctx retbty sevent =
  match sevent with
  | GuardEvent phi ->
      let phi = type_check_qualifier opctx ctx phi in
      GuardEvent phi
  | RetEvent pty ->
      let pty = pty_check opctx ctx pty in
      let _ =
        match retbty with
        | None ->
            _failatwith __FILE__ __LINE__
              "the pre-condition should not have return event"
        | Some retbty ->
            (* let () = *)
            (*   Printf.printf "%s: %s ?= %s\n" "ret" (Nt.layout retbty) *)
            (*     (Nt.layout (erase_pty pty)) *)
            (* in *)
            _check_equality __FILE__ __LINE__ Nt.eq retbty (erase_pty pty)
      in
      RetEvent pty
  | EffEvent { op; vs; v; phi } ->
      (* let () = Printf.printf "sevent: %s\n" (To_rty.layout_sevent sevent) in *)
      (* let () = *)
      (*   Printf.printf "vs: %s\n" (List.split_by_comma (fun x -> x.Nt.x) vs) *)
      (* in *)
      let opty = Aux.infer_op opctx (Op.EffOp op) in
      let argsty, retnty = Nt.destruct_arr_tp opty in
      let vs =
        List.map
          Nt.(
            fun ({ x; ty }, ty') ->
              (* let () = *)
              (*   Printf.printf "%s: %s ?= %s\n" op (Nt.layout ty) (Nt.layout ty') *)
              (* in *)
              let ty = _check_equality __FILE__ __LINE__ eq ty ty' in
              { x; ty })
          (_safe_combine __FILE__ __LINE__ vs argsty)
      in
      let retnty = _check_equality __FILE__ __LINE__ Nt.eq v.Nt.ty retnty in
      let v = Nt.{ x = v.x; ty = retnty } in
      let ctx' = Typectx.new_to_rights ctx (v :: vs) in
      let phi = type_check_qualifier opctx ctx' phi in
      EffEvent { op; vs; v; phi }

and regex_check opctx ctx retbty (regex : regex) : regex =
  match regex with
  | EpsilonA | AnyA | EmptyA -> regex
  | EventA se -> EventA (sevent_check opctx ctx retbty se)
  | LorA (t1, t2) ->
      LorA (regex_check opctx ctx retbty t1, regex_check opctx ctx retbty t2)
  | SetMinusA (t1, t2) ->
      SetMinusA
        (regex_check opctx ctx retbty t1, regex_check opctx ctx retbty t2)
  | LandA (t1, t2) ->
      LandA (regex_check opctx ctx retbty t1, regex_check opctx ctx retbty t2)
  | SeqA (t1, t2) ->
      SeqA (regex_check opctx ctx retbty t1, regex_check opctx ctx retbty t2)
  | StarA t -> StarA (regex_check opctx ctx retbty t)
  | ComplementA t -> ComplementA (regex_check opctx ctx retbty t)
