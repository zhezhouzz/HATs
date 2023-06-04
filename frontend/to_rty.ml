module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw
open Sugar

let pprint_id Nt.{ x; ty } = spf "%s:%s" x (Nt.layout ty)
let pprint_id_name Nt.{ x; _ } = x

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
let pprint_parn body = spf "{%s}" body
(* match ou with Over -> spf "{%s}" body | Under -> spf "[%s]" body *)

let tpA str = spf "⦇%s⦈" str
let tpEvent str = spf "⟨%s⟩" str
let layout_stropt = function None -> "" | Some x -> spf "%s:" x
let layout_arr = function PiArr -> "→" | SigamArr -> "⇢"

let rec pprint_pty rty =
  match rty with
  | BasePty { cty } -> pprint_parn (pprint_cty cty)
  | TuplePty ptys -> spf "(%s)" (List.split_by_comma pprint_pty ptys)
  | ArrPty { arr_kind = PiArr; rarg; retrty } ->
      spf "%s%s%s%s" (layout_stropt rarg.px) (pprint_pty rarg.pty)
        (layout_arr PiArr) (pprint_rty retrty)
  | ArrPty { arr_kind = SigamArr; rarg; retrty } ->
      spf "?%s%s%s%s" (layout_stropt rarg.px)
        (Nt.layout (erase_pty rarg.pty))
        (layout_arr SigamArr) (pprint_rty retrty)

and pprint_rty = function
  | Pty pty -> pprint_pty pty
  | Regty { nty; prereg; postreg } ->
      spf "[%s | %s ⇒ %s]" (Nt.layout nty) (pprint_regex prereg)
        (pprint_regex postreg)

and pprint_sevent = function
  | GuardEvent phi ->
      tpEvent @@ spf "%s %s" guard_name (To_qualifier.layout phi)
  | RetEvent pty -> tpEvent @@ spf "%s %s" ret_name (pprint_pty pty)
  | EffEvent { op; vs; phi } ->
      tpEvent
      @@ spf "%s(%s) | %s" op
           (List.split_by_comma pprint_id_name vs)
           (To_qualifier.layout phi)

and pprint_regex = function
  | EmptyA -> "∅"
  | EpsilonA -> "ϵ"
  | EventA se -> pprint_sevent se
  | LorA (a1, a2) -> spf "(%s ‖ %s)" (pprint_regex a1) (pprint_regex a2)
  | LandA (a1, a2) -> spf "(%s && %s)" (pprint_regex a1) (pprint_regex a2)
  | SeqA (a1, a2) -> spf "%s%s" (pprint_regex a1) (pprint_regex a2)
  | StarA a -> spf "(%s)*" (pprint_regex a)
  | AnyA -> "."
  | ComplementA a -> spf "(%s)ᶜ" (pprint_regex a)

let get_denoteopt_from_attr a =
  match a with [ x ] -> Some x.attr_name.txt | _ -> None

let get_denoteopt expr = get_denoteopt_from_attr expr.pexp_attributes

let get_denote expr =
  match get_denoteopt expr with
  | Some x -> x
  | None -> _failatwith __FILE__ __LINE__ ""

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
  | _ ->
      let () = Printf.printf "\nct: %s\n" (layout_coretype ct) in
      _failatwith __FILE__ __LINE__ ""

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

let rec mk_arrpty arr_kind pattern ptyexpr body =
  let id = To_pat.patten_to_typed_ids pattern in
  let px =
    match id with
    | [ id ] when String.equal id.x "_" -> None
    | [ id ] -> Some id.x
    | _ -> failwith "rty_of_ocamlexpr_aux"
  in
  let rarg = px #:: (pty_of_ocamlexpr_aux ptyexpr) in
  let retrty = rty_of_ocamlexpr_aux body in
  ArrPty { arr_kind; rarg; retrty }

and pty_of_ocamlexpr_aux expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ -> BasePty { cty = cty_of_ocamlexpr_aux expr }
    | Pexp_tuple es -> TuplePty (List.map aux es)
    | Pexp_fun (_, Some ptyexpr, pattern, body) ->
        mk_arrpty PiArr pattern ptyexpr body
    | Pexp_let (_, [ vb ], body) ->
        mk_arrpty SigamArr vb.pvb_pat vb.pvb_expr body
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
        if String.equal "epsilonA" id then EpsilonA
        else if String.equal "emptyA" id then EmptyA
        else if String.equal "anyA" id then AnyA
        else
          _failatwith __FILE__ __LINE__
            (spf "the automata var (%s) are disallowed" id)
    | Pexp_apply (func, args) -> (
        let f = To_expr.id_of_ocamlexpr func in
        let args = List.map snd args in
        match (f, args) with
        | "starA", [ e1 ] -> StarA (aux e1)
        | "compA", [ e1 ] -> ComplementA (aux e1)
        | "mu", _ ->
            _failatwith __FILE__ __LINE__
              "the recursive automata are disallowed"
        | "lorA", [ a; b ] -> LorA (aux a, aux b)
        | "landA", [ a; b ] -> LandA (aux a, aux b)
        | _, _ -> _failatwith __FILE__ __LINE__ @@ spf "unknown regular op %s" f
        )
    | Pexp_sequence (a, b) -> SeqA (aux a, aux b)
    | Pexp_construct _ -> EventA (sevent_of_ocamlexpr_aux expr)
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux expr

and rty_of_ocamlexpr_aux expr =
  match expr.pexp_desc with
  | Pexp_record ([ (id1, e1); (id2, e2) ], None) ->
      let id1 = To_id.longid_to_id id1 in
      let id2 = To_id.longid_to_id id2 in
      let () =
        _assert __FILE__ __LINE__ "syntax error: {pre = ...; post = ...}"
          (String.equal id1 "pre" && String.equal id2 "post")
      in
      let prereg = regex_of_ocamlexpr_aux e1 in
      let nty, postreg =
        match e2.pexp_desc with
        | Pexp_constraint (e, ct) ->
            (Type.core_type_to_t ct, regex_of_ocamlexpr_aux e)
        | _ ->
            _failatwith __FILE__ __LINE__
              "syntax error: the post type must be typed"
      in
      Regty { nty; prereg; postreg }
  | _ -> Pty (pty_of_ocamlexpr_aux expr)

let rty_of_ocamlexpr expr =
  let rty = rty_of_ocamlexpr_aux expr in
  normalize_name_rty rty

let layout = pprint_rty
let layout_cty = pprint_cty
let layout_pty = pprint_pty
let layout_regex = pprint_regex
let layout_sevent = pprint_sevent
