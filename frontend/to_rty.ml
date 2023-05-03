module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw
open Sugar

let pprint_id Nt.{ x; ty } = spf "%s:%s" x (Nt.layout ty)

let pprint_phi v (phi : P.t) =
  let open P in
  match phi with
  | Pred
      (MethodPred
        ({ x = "=="; _ }, [ { x = AVar id; _ }; { x = AC (Constant.I i); _ } ]))
    when String.equal v.Nt.x id ->
      spf "%i" i
  | Pred
      (MethodPred
        ({ x = "=="; _ }, [ { x = AVar id; _ }; { x = AC (Constant.B b); _ } ]))
    when String.equal v.Nt.x id ->
      spf "%b" b
  | _ -> To_qualifier.layout phi

let pprint_cty { v; phi } = spf "%s | %s" (pprint_id v) (pprint_phi v phi)

let pprint_ou ou body =
  match ou with Over -> spf "{%s}" body | Under -> spf "[%s]" body

let rec pprint_pty rty =
  match rty with
  | BasePty { ou; cty } -> pprint_ou ou (pprint_cty cty)
  | TuplePty ptys -> spf "(%s)" (List.split_by_comma pprint_pty ptys)
  | ArrPty { rarg; retrty } ->
      let x = match rarg.px with None -> "" | Some x -> spf "%s:" x in
      spf "%s%s→%s" x (pprint_pty rarg.pty) (pprint_rty retrty)

and pprint_rty = function
  | Pty pty -> pprint_pty pty
  | Regty Nt.{ x = regty; ty } ->
      spf "⟨%s | %s⟩" (Nt.layout ty) (pprint_regty regty)

and pprint_sevent = function
  | RetEvent pty -> spf "[Ret %s]" (pprint_pty pty)
  | EffEvent { op; vs; phi } ->
      spf "[%s (%s) | %s]" op
        (List.split_by_comma pprint_id vs)
        (To_qualifier.layout phi)

and pprint_regty = function
  | EpsilonA -> "ϵ"
  | EventA se -> pprint_sevent se
  | LorA (a1, a2) -> spf "(%s ‖ %s)" (pprint_regty a1) (pprint_regty a2)
  | SeqA (a1, a2) -> spf "%s%s" (pprint_regty a1) (pprint_regty a2)
  | StarA a -> spf "(%s)*" (pprint_regty a)
  | CtxA { gamma; regty } ->
      spf "Σ(%s),%s"
        (List.split_by_comma
           (fun { cx; cty } -> spf "%s:[%s]" cx (pprint_cty cty))
           gamma)
        (pprint_regty regty)

let get_denote expr =
  match expr.pexp_attributes with
  | [ x ] -> x.attr_name.txt
  | _ -> _failatwith __FILE__ __LINE__ ""

let get_ou expr =
  match get_denote expr with
  | "over" -> Over
  | "under" -> Under
  | _ -> _failatwith __FILE__ __LINE__ ""

let get_op expr =
  match To_op.string_to_op (get_denote expr) with
  | Some (Op.DtOp op) -> op
  | _ -> _failatwith __FILE__ __LINE__ "die"

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
  aux expr

let cty_of_ocamlexpr expr =
  match vars_phi_of_ocamlexpr expr with
  | [ v ], phi -> { v; phi }
  | _ -> _failatwith __FILE__ __LINE__ "die"

let rec pty_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ ->
        let ou = get_ou expr in
        BasePty { ou; cty = cty_of_ocamlexpr expr }
    | Pexp_tuple es -> TuplePty (List.map aux es)
    | Pexp_let (_, [ vb ], body) ->
        let id = To_pat.patten_to_typed_ids vb.pvb_pat in
        let rx =
          match id with
          | [ id ] when String.equal id.x "_" -> None
          | [ id ] -> Some id.x
          | _ -> failwith "rty_of_ocamlexpr"
        in
        let rarg_rty = aux vb.pvb_expr in
        let rarg = rx #:: rarg_rty in
        ArrPty { rarg; retrty = rty_of_ocamlexpr body }
    | _ ->
        _failatwith __FILE__ __LINE__
          (spf "wrong refinement type: %s"
             (Pprintast.string_of_expression expr))
  in
  aux expr

and sevent_of_ocamlexpr expr =
  match expr.pexp_desc with
  | Pexp_constraint _ -> (
      let op = get_op expr in
      match op with
      | "Ret" ->
          let pty = pty_of_ocamlexpr expr in
          RetEvent pty
      | _ ->
          let vs, phi = vars_phi_of_ocamlexpr expr in
          EffEvent { op; vs; phi })
  | _ -> _failatwith __FILE__ __LINE__ "die"

and regty_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_ident id ->
        if String.equal "epsilon" @@ To_id.longid_to_id id then EpsilonA
        else _failatwith __FILE__ __LINE__ "die"
    | Pexp_apply (func, args) -> (
        let f = To_expr.id_of_ocamlexpr func in
        let args = List.map snd args in
        match (f.x, args) with
        | "star", [ e1 ] -> StarA (aux e1)
        | "sigma", [ { pexp_desc = Pexp_array es; _ }; e2 ] ->
            let gamma =
              List.map
                (fun e ->
                  match e.pexp_desc with
                  | Pexp_tuple [ cx; cty ] ->
                      let cx = (To_expr.id_of_ocamlexpr cx).P.x in
                      let cty = cty_of_ocamlexpr cty in
                      { cx; cty }
                  | _ -> _failatwith __FILE__ __LINE__ "die")
                es
            in
            CtxA { gamma; regty = aux e2 }
        | "||", [ a; b ] -> LorA (aux a, aux b)
        | _, _ -> _failatwith __FILE__ __LINE__ "die")
    | Pexp_sequence (a, b) -> SeqA (aux a, aux b)
    | Pexp_constraint _ -> EventA (sevent_of_ocamlexpr expr)
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux expr

and rty_of_ocamlexpr expr =
  match expr.pexp_desc with
  | Pexp_constraint (e, ct) -> (
      let ty = Type.core_type_to_t ct in
      let kind = get_op expr in
      match kind with
      | "Regty" -> Regty Nt.{ x = regty_of_ocamlexpr e; ty }
      | _ -> Pty (pty_of_ocamlexpr expr))
  | _ -> Pty (pty_of_ocamlexpr expr)

(* let rty_of_ocamlexpr expr = *)
(*   let rec aux expr = *)
(*     match expr.pexp_desc with *)
(*     | Pexp_let (_, [ vb ], body) -> *)
(*         let id = To_pat.patten_to_typed_ids vb.pvb_pat in *)
(*         let rx = *)
(*           match id with *)
(*           | [ id ] when String.equal id.x "_" -> None *)
(*           | [ id ] -> Some id.x *)
(*           | _ -> failwith "rty_of_ocamlexpr" *)
(*         in *)
(*         let rarg_rty = aux vb.pvb_expr in *)
(*         let rarg = rx #: rarg_rty in *)
(*         let dep, label = get_dep_label vb in *)
(*         ArrPty { dep; label; rarg; retrty = aux body } *)
(*     | Pexp_constraint _ -> *)
(*         let ou = get_ou expr in *)
(*         BasePty { ou; cty = cty_of_ocamlexpr expr } *)
(*     | Pexp_record (_, Some _) -> failwith "rty_of_ocamlexpr" *)
(*     | Pexp_record (cases, None) -> *)
(*         let cases = *)
(*           List.map (fun (x, expr) -> (To_pat.longid_to_id x, expr)) cases *)
(*         in *)
(*         let find id = *)
(*           snd @@ List.find (fun (x, _) -> String.equal id x) cases *)
(*         in *)
(*         let h = To_expr.id_of_ocamlexpr (find "h") in *)
(*         let pre = cty_of_ocamlexpr (find "pre") in *)
(*         let post = cty_of_ocamlexpr (find "post") in *)
(*         let rty = aux (find "rty") in *)
(*         Traced { h; pre; rty; post } *)
(*     (\* | Pexp_setfield (phi, h, rty) -> *\) *)
(*     (\*     let phi = To_qualifier.qualifier_of_ocamlexpr phi in *\) *)
(*     (\*     let h = To_pat.longid_to_id h in *\) *)
(*     (\*     let rty = aux rty in *\) *)
(*     (\*     mk_traced h phi rty *\) *)
(*     | _ -> *)
(*         _failatwith __FILE__ __LINE__ *)
(*           (spf "wrong refinement type: %s" *)
(*              (Pprintast.string_of_expression expr)) *)
(*   in *)
(*   aux expr *)

let layout = pprint_rty
let layout_cty = pprint_cty
let layout_pty = pprint_pty
let layout_regty = pprint_regty
