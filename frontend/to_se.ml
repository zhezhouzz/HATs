module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw.SE
open Sugar
open Aux

let tpEvent str = spf "⟨%s⟩" str

let pprint = function
  | GuardEvent phi -> tpEvent @@ To_qualifier.layout phi
  | EffEvent { op; vs; v; phi } ->
      tpEvent
      @@ spf "%s %s = %s | %s" op
           (List.split_by " " (fun x -> x.x) vs)
           v.x (To_qualifier.layout phi)

let layout = pprint

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

let desugar_sevent expr =
  match expr.pexp_desc with
  | Pexp_tuple es ->
      let es, ephi = Aux.force_last es in
      let phi = To_qualifier.qualifier_of_ocamlexpr ephi in
      let es =
        List.map
          (fun e ->
            let x = To_expr.id_of_ocamlexpr e in
            match get_denoteopt e with
            | None -> (x, None)
            | Some "d" ->
                let op_eq = { x = Op.BuiltinOp "=="; ty = None } in
                let arg = Rename.unique "x" in
                let arg' = { x = AVar arg; ty = None } in
                let x = { x = AVar x; ty = None } in
                (arg, Some (Lit (AAppOp (op_eq, [ arg'; x ]))))
            | _ -> _failatwith __FILE__ __LINE__ "die")
          es
      in
      let phi' =
        List.fold_left
          (fun res (_, prop) ->
            match prop with None -> res | Some prop -> smart_add_to prop res)
          mk_true es
      in
      let args, v =
        Aux.force_last @@ List.map (fun x -> x #: None) @@ List.map fst es
      in
      (args, v, smart_add_to phi' phi)
  | _ -> _failatwith __FILE__ __LINE__ "die"

let of_ocamlexpr_aux expr =
  match expr.pexp_desc with
  | Pexp_construct (op, Some e) -> (
      (* symbolic operator event *)
      let op = To_id.longid_to_id op in
      match op with
      | "Any" ->
          (* symbolic global event *)
          let phi = To_qualifier.qualifier_of_ocamlexpr e in
          GuardEvent phi
      | _ ->
          let vs, v, phi = desugar_sevent e in
          EffEvent { op; vs; v; phi })
  | _ -> _failatwith __FILE__ __LINE__ "die"

let of_ocamlexpr expr =
  let rty = of_ocamlexpr_aux expr in
  let rty = normalize_name rty in
  (* let () = Printf.printf "ZZ: %s\n" (pprint_rty rty) in *)
  rty
