open Ocaml_parser
open Parsetree
module Type = Normalty.Frontend
open Ast
module L = Termlang

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

let rec pattern_to_slang pattern =
  match pattern.ppat_desc with
  | Ppat_tuple ps -> L.make_untyped @@ L.Tu (List.map pattern_to_slang ps)
  | Ppat_var ident -> L.make_untyped @@ L.Var ident.txt
  | Ppat_constraint (ident, tp) ->
      (* let () = *)
      (*   Printf.printf "paring id:%s tp:%s\n" (layout_ ident) (Type.layout_ tp) *)
      (* in *)
      let term = pattern_to_slang ident in
      L.{ ty = Some (Type.core_type_to_notated_t tp); x = term.x }
  | Ppat_construct (c, args) ->
      let c =
        match Longident.flatten c.txt with
        | [ c ] -> (
            match c with
            | "Exn" -> L.{ ty = Some (None, Ty_unknown); x = Exn }
            | "true" ->
                L.{ ty = Some (None, Ty_bool); x = Const (Ast.Value.B true) }
            | "false" ->
                L.{ ty = Some (None, Ty_bool); x = Const (Ast.Value.B false) }
            | _ -> L.make_untyped @@ L.Var c)
        | _ -> failwith "unimp: long name"
      in
      let res =
        match args with
        | None -> L.App (c, [])
        | Some arg -> (
            let arg = pattern_to_slang arg in
            match (arg.L.ty, arg.L.x) with
            | None, L.Tu args -> L.App (c, args) (* NOTE: here we decurry *)
            | None, L.Var _ -> L.App (c, [ arg ])
            | _ -> failwith "pat die")
      in
      L.make_untyped res
  | Ppat_any -> L.make_untyped @@ L.Var "_"
  | _ ->
      Pprintast.pattern Format.std_formatter pattern;
      failwith "wrong pattern name, maybe untyped"

let rec slang_to_pattern slang = dest_to_pat @@ slang_to_pattern_desc slang

and slang_to_pattern_desc_untyped slang =
  match slang with
  | L.Var name ->
      let pat = Ppat_var (Location.mknoloc name) in
      pat
  | L.Tu ss -> Ppat_tuple (List.map slang_to_pattern ss)
  | L.App (c, arg) -> (
      let c =
        match c.L.x with
        | L.Var name -> (
            match Longident.unflatten [ name ] with
            | Some x -> Location.mknoloc x
            | _ -> failwith "die: pat")
        | _ -> failwith "pat die"
      in
      match arg with
      | [] -> Ppat_construct (c, None)
      | [ arg ] -> Ppat_construct (c, Some (slang_to_pattern arg))
      | _ ->
          Ppat_construct
            (c, Some (slang_to_pattern (L.make_untyped @@ L.Tu arg))))
  | _ -> failwith "wrong pattern name, maybe untyped"

and slang_to_pattern_desc slang =
  match slang.L.ty with
  | None -> slang_to_pattern_desc_untyped slang.L.x
  | Some ty ->
      let ty = Type.notated_t_to_core_type ty in
      let pat = dest_to_pat @@ slang_to_pattern_desc_untyped slang.L.x in
      (* let () = *)
      (*   Printf.printf "layout id:%s tp:%s\n" (layout_ pat) (Type.layout_ ty) *)
      (* in *)
      Ppat_constraint (pat, ty)

(* TODO: Check nested tuple *)
let to_typed_slang x =
  let open L in
  let rec aux l x =
    match x.x with
    | Var name -> l @ [ { ty = x.ty; x = name } ]
    | Tu xs -> List.fold_left aux l xs
    | _ -> failwith "not a patten"
  in
  aux [] x

let patten_to_typed_ids pattern = to_typed_slang @@ pattern_to_slang pattern

let typed_ids_to_pattens ids =
  let open L in
  let l = List.map (fun x -> { x = Var x.x; ty = x.ty }) ids in
  let e =
    match l with
    | [] -> failwith "die"
    | [ a ] -> a
    | l -> { x = Tu l; ty = None }
  in
  slang_to_pattern e
