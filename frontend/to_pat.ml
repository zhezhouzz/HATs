open Ocaml5_parser
open Parsetree
module T = Syntax.Nt
open Syntax
open StructureRaw
open Sugar

let layout_ t =
  let _ = Format.flush_str_formatter () in
  Pprintast.pattern Format.str_formatter t;
  Format.flush_str_formatter ()

let dest_to_pat pat =
  {
    ppat_desc = pat;
    ppat_loc = Location.none;
    ppat_loc_stack = [];
    ppat_attributes = [];
  }

let tupdate ty { x; _ } = { x; ty }

type term_or_op = C_is_term of term typed | C_is_op of Op.t typed

let constructor_to_term_or_op c : term_or_op =
  match c with
  | "Err" -> C_is_term Err #: (Some T.Ty_any)
  | "true" -> C_is_term (mk_bool true)
  | "false" -> C_is_term (mk_bool false)
  | "()" -> C_is_term mk_unit
  | name -> (
      match To_op.string_to_op name with
      | None -> _failatwith __FILE__ __LINE__ "die: pat"
      | Some op -> C_is_op op #: None)

let rec pattern_to_term pattern =
  match pattern.ppat_desc with
  | Ppat_tuple ps -> mk_noty @@ Tu (List.map pattern_to_term ps)
  | Ppat_var ident -> mk_var ident.txt
  | Ppat_constraint (ident, tp) ->
      let term = pattern_to_term ident in
      term.x #: (Some (Normalty.Frontend.core_type_to_t tp))
  | Ppat_construct (c, args) -> (
      let c = To_id.longid_to_id c in
      match constructor_to_term_or_op c with
      | C_is_term tm -> tm
      | C_is_op op ->
          let args =
            match args with
            | None -> []
            | Some args -> de_typed_tuple @@ pattern_to_term @@ snd args
          in
          (AppOp (op, args)) #: None)
  | Ppat_any -> mk_var "_"
  | _ ->
      Pprintast.pattern Format.std_formatter pattern;
      failwith "wrong pattern name, maybe untyped"

let rec term_to_pattern slang = dest_to_pat @@ term_to_pattern_desc slang

and term_to_pattern_desc_untyped slang =
  match slang with
  | Var name ->
      let pat = Ppat_var (Location.mknoloc name) in
      pat
  | Tu ss -> Ppat_tuple (List.map term_to_pattern ss)
  | AppOp (name, arg) -> (
      let c = To_id.id_to_longid (To_op.op_to_string name.x) in
      match arg with
      | [] -> Ppat_construct (c, None)
      | [ arg ] -> Ppat_construct (c, Some ([], term_to_pattern arg))
      | _ -> Ppat_construct (c, Some ([], term_to_pattern (mk_noty @@ Tu arg))))
  | _ -> failwith "wrong pattern name, maybe untyped"

and term_to_pattern_desc slang =
  match slang.ty with
  | None -> term_to_pattern_desc_untyped slang.x
  | Some ty ->
      let ty = Normalty.Frontend.t_to_core_type ty in
      let pat = dest_to_pat @@ term_to_pattern_desc_untyped slang.x in
      (* let () = *)
      (*   Printf.printf "layout id:%s tp:%s\n" (layout_ pat) (Type.layout_ ty) *)
      (* in *)
      Ppat_constraint (pat, ty)

(* TODO: Check nested tuple *)
let to_typed_ids x =
  let rec aux l x =
    match x.x with
    | Var name -> l @ [ { ty = x.ty; x = name } ]
    | Tu xs -> List.fold_left aux l xs
    | _ -> failwith "not a patten"
  in
  aux [] x

let patten_to_typed_ids pattern = to_typed_ids @@ pattern_to_term pattern

open Sugar

let typed_ids_to_pattern ids =
  let l = List.map (fun x -> { x = Var x.x; ty = x.ty }) ids in
  let e =
    match l with
    | [] -> failwith "die"
    | [ a ] -> a
    | l ->
        let tys = List.map (fun a -> a.ty) l in
        (Tu l) #: (opt_fmap (opt_list_to_list_opt tys) (fun x -> T.Ty_tuple x))
  in
  term_to_pattern e
