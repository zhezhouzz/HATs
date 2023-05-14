module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw
open Sugar

let pprint_id Nt.{ x; ty } = spf "%s:%s" x (Nt.layout ty)

let pprint_phi v (phi : P.prop) =
  let open P in
  match phi with
  | Lit
      (AAppOp
        ( { x = Op.BuiltinOp "=="; _ },
          [ { x = AVar id; _ }; { x = AC (Constant.I i); _ } ] ))
    when String.equal v.Nt.x id ->
      spf "%i" i
  | Lit
      (AAppOp
        ( { x = Op.BuiltinOp "=="; _ },
          [ { x = AVar id; _ }; { x = AC (Constant.B b); _ } ] ))
    when String.equal v.Nt.x id ->
      spf "%b" b
  | _ -> To_qualifier.layout phi

let pprint_cty { v; phi } = spf "%s | %s" (pprint_id v) (pprint_phi v phi)

let pprint_ou ou body =
  match ou with Over -> spf "{%s}" body | Under -> spf "[%s]" body

let tpA str = spf "⦇%s⦈" str
let tpEvent str = spf "⟨%s⟩" str
let layout_stropt = function None -> "" | Some x -> spf "%s:" x

let rec pprint_pty rty =
  match rty with
  | BasePty { ou; cty } -> pprint_ou ou (pprint_cty cty)
  | TuplePty ptys -> spf "(%s)" (List.split_by_comma pprint_pty ptys)
  | ArrPty { rarg; retrty } ->
      spf "%s%s→%s" (layout_stropt rarg.px) (pprint_pty rarg.pty)
        (pprint_rty retrty)

and pprint_rty = function
  | Pty pty -> pprint_pty pty
  | Regty Nt.{ x = regex; ty } ->
      tpA @@ spf "%s | %s" (Nt.layout ty) (pprint_regex regex)

and pprint_sevent = function
  | GuardEvent phi ->
      tpEvent @@ spf "%s %s" guard_name (To_qualifier.layout phi)
  | RetEvent pty -> tpEvent @@ spf "%s %s" ret_name (pprint_pty pty)
  | EffEvent { op; vs; phi } ->
      tpEvent
      @@ spf "%s (%s) | %s" op
           (List.split_by_comma pprint_id vs)
           (To_qualifier.layout phi)

and pprint_regex = function
  | EpsilonA -> "ϵ"
  | EventA se -> pprint_sevent se
  | LorA (a1, a2) -> spf "(%s ‖ %s)" (pprint_regex a1) (pprint_regex a2)
  | LandA (a1, a2) -> spf "(%s && %s)" (pprint_regex a1) (pprint_regex a2)
  | SeqA (a1, a2) -> spf "%s%s" (pprint_regex a1) (pprint_regex a2)
  | StarA a -> spf "(%s)*" (pprint_regex a)
  | SigmaA { localx; xA; body } ->
      spf "Σ%s:%s.%s" localx.x (pprint_regex xA) (pprint_regex body)

let get_denoteopt_from_attr a =
  match a with [ x ] -> Some x.attr_name.txt | _ -> None

let get_denoteopt expr = get_denoteopt_from_attr expr.pexp_attributes

let get_denote expr =
  match get_denoteopt expr with
  | Some x -> x
  | None -> _failatwith __FILE__ __LINE__ ""

let get_ou expr =
  match get_denoteopt expr with
  | Some "over" -> Over
  | Some "under" -> Under
  | None -> Under
  | _ -> _failatwith __FILE__ __LINE__ ""

let get_opopt expr =
  match To_op.string_to_op (get_denote expr) with
  | Some (Op.DtOp op) -> Some op
  | _ -> None

let get_op expr =
  match get_opopt expr with
  | Some x -> x
  | None -> _failatwith __FILE__ __LINE__ "die"

let get_self ct =
  let open Nt in
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> name.txt #: (Type.core_type_to_t ty)
  | _ -> _failatwith __FILE__ __LINE__ ""

let vars_phi_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint (e', ct) ->
        let v = get_self ct in
        let vs, phi = aux e' in
        (v :: vs, phi)
    | _ -> ([], To_qualifier.qualifier_of_ocamlexpr expr)
  in
  let vs, prop = aux expr in
  (List.rev vs, prop)

let cty_of_ocamlexpr_aux expr =
  match vars_phi_of_ocamlexpr expr with
  | [ v ], phi -> { v; phi }
  | _ -> _failatwith __FILE__ __LINE__ "die"

let rec pty_of_ocamlexpr_aux expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ ->
        let ou = get_ou expr in
        BasePty { ou; cty = cty_of_ocamlexpr_aux expr }
    | Pexp_tuple es -> TuplePty (List.map aux es)
    | Pexp_fun (_, Some pty, px, body) ->
        let id = To_pat.patten_to_typed_ids px in
        let px =
          match id with
          | [ id ] when String.equal id.x "_" -> None
          | [ id ] -> Some id.x
          | _ -> failwith "rty_of_ocamlexpr_aux"
        in
        let rarg = px #:: (aux pty) in
        let retrty = rty_of_ocamlexpr_aux body in
        ArrPty { rarg; retrty }
    (* | Pexp_let (_, [ vb ], body) -> *)
    (*     let id = To_pat.patten_to_typed_ids vb.pvb_pat in *)
    (*     let rx = *)
    (*       match id with *)
    (*       | [ id ] when String.equal id.x "_" -> None *)
    (*       | [ id ] -> Some id.x *)
    (*       | _ -> failwith "rty_of_ocamlexpr_aux" *)
    (*     in *)
    (*     let rarg_rty = aux vb.pvb_expr in *)
    (*     let rarg = rx #:: rarg_rty in *)
    (*     ArrPty { rarg; retrty = rty_of_ocamlexpr_aux body } *)
    | _ ->
        _failatwith __FILE__ __LINE__
          (spf "wrong refinement type: %s"
             (Pprintast.string_of_expression expr))
  in
  aux expr

and sevent_of_ocamlexpr_aux expr =
  match expr.pexp_desc with
  | Pexp_construct (op, Some e) ->
      let op = To_id.longid_to_id op in
      if String.equal op guard_name then
        GuardEvent (To_qualifier.qualifier_of_ocamlexpr e)
      else if String.equal op ret_name then RetEvent (pty_of_ocamlexpr_aux e)
      else
        let vs, phi = vars_phi_of_ocamlexpr e in
        EffEvent { op; vs; phi }
  | _ -> _failatwith __FILE__ __LINE__ "die"

and regex_of_ocamlexpr_aux expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_ident id ->
        let id = To_id.longid_to_id id in
        if String.equal "epsilon" id then EpsilonA
        else
          _failatwith __FILE__ __LINE__
            (spf "the automata var (%s) are disallowed" id)
    | Pexp_let (_, [ vb ], body) ->
        let id = To_pat.patten_to_typed_ids vb.pvb_pat in
        let localx =
          match id with
          | [ { x; ty = Some ty } ] -> Nt.{ x; ty }
          | _ -> failwith "rty_of_ocamlexpr_aux"
        in
        SigmaA { localx; xA = aux vb.pvb_expr; body = aux body }
    | Pexp_apply (func, args) -> (
        let f = To_expr.id_of_ocamlexpr func in
        let args = List.map snd args in
        match (f, args) with
        | "star", [ e1 ] -> StarA (aux e1)
        (* | "sigma", [ e1; e2; e3 ] -> *)
        (*     let cx = To_expr.id_of_ocamlexpr e1 in *)
        (*     let cty = cty_of_ocamlexpr_aux e2 in *)
        (*     Sigmaty { localx = { cx; cty }; regex = aux e3 } *)
        | "mu", _ ->
            _failatwith __FILE__ __LINE__
              "the recursive automata are disallowed"
            (* let mux = To_expr.id_of_ocamlexpr mux in *)
            (* let muA = To_expr.id_of_ocamlexpr muA in *)
            (* let index = To_lit.lit_of_ocamlexpr_aux index in *)
            (* let regex = aux regex in *)
            (* RecA { mux; muA; index; regex } *)
        | "lorA", [ a; b ] -> LorA (aux a, aux b)
        | "landA", [ a; b ] -> LandA (aux a, aux b)
        | _, _ -> _failatwith __FILE__ __LINE__ "die")
    | Pexp_sequence (a, b) -> SeqA (aux a, aux b)
    | Pexp_construct _ -> EventA (sevent_of_ocamlexpr_aux expr)
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux expr

and rty_of_ocamlexpr_aux expr =
  match expr.pexp_desc with
  (* | Pexp_let (_, [ vb ], body) -> *)
  (*     let id = To_pat.patten_to_typed_ids vb.pvb_pat in *)
  (*     let rx = *)
  (*       match id with [ id ] -> id.x | _ -> failwith "rty_of_ocamlexpr_aux" *)
  (*     in *)
  (*     let rty = rty_of_ocamlexpr_aux vb.pvb_expr in *)
  (*     let localx = rx #: rty in *)
  (*     Sigmaty { localx; rty = rty_of_ocamlexpr_aux body } *)
  | _ -> (
      match expr.pexp_desc with
      | Pexp_constraint (e, ct) -> (
          match get_denoteopt_from_attr ct.ptyp_attributes with
          | Some "regex" ->
              let ty = Type.core_type_to_t ct in
              Regty Nt.{ x = regex_of_ocamlexpr_aux e; ty }
          | _ -> Pty (pty_of_ocamlexpr_aux expr))
      | _ -> Pty (pty_of_ocamlexpr_aux expr))

let rty_of_ocamlexpr expr =
  let rty = rty_of_ocamlexpr_aux expr in
  normalize_name_rty rty

let layout = pprint_rty
let layout_cty = pprint_cty
let layout_pty = pprint_pty
let layout_regex = pprint_regex
