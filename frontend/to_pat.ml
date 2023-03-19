open Ocaml_parser
open Parsetree
module T = Language.Ty
open Language.OptTypedTermlang

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

let rec pattern_to_term pattern =
  match pattern.ppat_desc with
  | Ppat_tuple ps -> mk_noty @@ Tu (List.map pattern_to_term ps)
  | Ppat_var ident -> mk_var ident.txt
  | Ppat_constraint (ident, tp) ->
      let term = pattern_to_term ident in
      term.x #: (Some (Normalty.Frontend.core_type_to_t tp))
  | Ppat_construct (c, args) -> (
      match (Longident.flatten c.txt, args) with
      | [ c ], None -> (
          match c with
          | "Err" -> Err #: (Some T.Ty_any)
          | "true" -> mk_bool true
          | "false" -> mk_bool false
          | name -> (AppOp (name #: None, [])) #: None)
      | [ name ], Some args ->
          let args = de_typed_tuple @@ pattern_to_term @@ snd args in
          (AppOp (name #: None, args)) #: None
      | _ -> failwith "unimp: long name")
  | Ppat_any -> mk_var "_"
  | _ ->
      Pprintast.pattern Format.std_formatter pattern;
      failwith "wrong pattern name, maybe untyped"

let rec slang_to_pattern slang = dest_to_pat @@ slang_to_pattern_desc slang

and slang_to_pattern_desc_untyped slang =
  match slang with
  | Var name ->
      let pat = Ppat_var (Location.mknoloc name) in
      pat
  | Tu ss -> Ppat_tuple (List.map slang_to_pattern ss)
  | AppOp (name, arg) -> (
      let c =
        match Longident.unflatten [ name.x ] with
        | Some x -> Location.mknoloc x
        | _ -> failwith "die: pat"
      in
      match arg with
      | [] -> Ppat_construct (c, None)
      | [ arg ] -> Ppat_construct (c, Some ([], slang_to_pattern arg))
      | _ -> Ppat_construct (c, Some ([], slang_to_pattern (mk_noty @@ Tu arg)))
      )
  | _ -> failwith "wrong pattern name, maybe untyped"

and slang_to_pattern_desc slang =
  match slang.ty with
  | None -> slang_to_pattern_desc_untyped slang.x
  | Some ty ->
      let ty = Normalty.Frontend.t_to_core_type ty in
      let pat = dest_to_pat @@ slang_to_pattern_desc_untyped slang.x in
      (* let () = *)
      (*   Printf.printf "layout id:%s tp:%s\n" (layout_ pat) (Type.layout_ ty) *)
      (* in *)
      Ppat_constraint (pat, ty)

(* TODO: Check nested tuple *)
let to_typed_slang x =
  let rec aux l x =
    match x.x with
    | Var name -> l @ [ { ty = x.ty; x = name } ]
    | Tu xs -> List.fold_left aux l xs
    | _ -> failwith "not a patten"
  in
  aux [] x

let patten_to_typed_ids pattern = to_typed_slang @@ pattern_to_term pattern

let typed_ids_to_pattens ids =
  let l = List.map (fun x -> { x = Var x.x; ty = x.ty }) ids in
  let e =
    match l with
    | [] -> failwith "die"
    | [ a ] -> a
    | l -> { x = Tu l; ty = None }
  in
  slang_to_pattern e
