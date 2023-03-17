module MetaEnv = Env
open Ocaml_parser
open Parsetree
open Zzdatatype.Datatype
module T = Ast.Termlang
module L = Ast.UT
module Ntyped = Ast.Ntyped
module Type = Normalty.Frontend
open Sugar

type mode = Under | Tuple

open L

let ot_pretty_layout x =
  match x with
  | { basename; prop = Autov.Prop.(MethodPred ("==", [ AVar id; ACint i ])); _ }
    when String.equal basename id.x ->
      Sugar.spf "{%i}" i
  | {
   basename;
   prop = Autov.Prop.(MethodPred ("==", [ AVar id; ACbool b ]));
   _;
  }
    when String.equal basename id.x ->
      Sugar.spf "{%b}" b
  | { basename; normalty; prop } ->
      Sugar.spf "{%s:%s | %s}" basename (Type.layout normalty)
        (Autov.pretty_layout_prop prop)

let pretty_layout x =
  let rec aux x =
    match x with
    | UnderTy_base
        {
          basename;
          prop = Autov.Prop.(MethodPred ("==", [ AVar id; ACint i ]));
          _;
        }
      when String.equal basename id.x ->
        Sugar.spf "[%i]" i
    | UnderTy_base
        {
          basename;
          prop = Autov.Prop.(MethodPred ("==", [ AVar id; ACbool b ]));
          _;
        }
      when String.equal basename id.x ->
        Sugar.spf "[%b]" b
    | UnderTy_base { basename; normalty; prop } ->
        Sugar.spf "[%s:%s | %s]" basename (Type.layout normalty)
          (Autov.pretty_layout_prop prop)
    | UnderTy_under_arrow { argty; retty } ->
        let arg_str = aux argty in
        let arg_str =
          if Ast.UT.is_base_type argty then arg_str else spf "(%s)" arg_str
        in
        Sugar.spf "%s→%s" arg_str (aux retty)
    | UnderTy_over_arrow { argname; argty; retty } ->
        Sugar.spf "%s→%s"
          (spf "%s:%s" argname (ot_pretty_layout argty))
          (aux retty)
    | UnderTy_tuple ts ->
        (* let () = Printf.printf "len(ts) = %i\n" @@ List.length ts in *)
        Sugar.spf "(%s)" @@ Zzdatatype.Datatype.List.split_by_comma aux ts
  in
  aux x

let prop_of_ocamlexpr e =
  let prop = Autov.prop_of_ocamlexpr e in
  let _ = Autov.Prop.assume_tope_uprop __FILE__ __LINE__ prop in
  prop

type rty_mode = RtyModeUnder | RtyModeOver
type base_rty = BaseRtyUnder of t | BaseRtyOver of ot

let get_mode expr =
  match expr.pexp_attributes with
  | [ x ] when String.equal x.attr_name.txt "over" -> RtyModeOver
  | [ x ] when String.equal x.attr_name.txt "under" -> RtyModeUnder
  | _ -> _failatwith __FILE__ __LINE__ ""

let baserty_of_ocamlexpr expr =
  match expr.pexp_desc with
  | Pexp_constraint (e, ct) -> (
      let basename, normalty =
        match Type.core_type_to_notated_t ct with
        | Some basename, normalty -> (basename, normalty)
        | _ -> _failatwith __FILE__ __LINE__ ""
      in
      let mode = get_mode expr in
      (* let _ = *)
      (*   Printf.printf "len(%s) = %i\n" (Pprintast.string_of_expression expr) *)
      (*   @@ List.length expr.pexp_attributes *)
      (* in *)
      let prop = prop_of_ocamlexpr e in
      match mode with
      | RtyModeOver -> BaseRtyOver { basename; normalty; prop }
      | RtyModeUnder -> BaseRtyUnder (UnderTy_base { basename; normalty; prop })
      )
  | _ -> _failatwith __FILE__ __LINE__ ""

let to_under_rty = function
  | BaseRtyUnder x -> x
  | _ -> _failatwith __FILE__ __LINE__ ""

let to_over_rty = function
  | BaseRtyUnder x -> x
  | _ -> _failatwith __FILE__ __LINE__ ""

let ot_undertype_of_ocamlexpr expr = to_over_rty @@ baserty_of_ocamlexpr expr

let _check_eq_nt file line t1 t2 =
  try _check_equality file line Ast.NT.eq t1 t2
  with e ->
    ( MetaEnv.show_debug_info @@ fun _ ->
      Printf.printf "Type %s != %s\n" (Type.layout t1) (Type.layout t2) );
    raise e

let undertype_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_tuple es ->
        BaseRtyUnder
          (L.UnderTy_tuple (List.map (fun x -> to_under_rty @@ aux x) es))
    | Pexp_let (_, [ vb ], body) -> (
        let id = Pat.patten_to_typed_ids vb.pvb_pat in
        let argname =
          match id with [ id ] -> id | _ -> failwith "undertype_of_ocamlexpr"
        in
        match aux vb.pvb_expr with
        | BaseRtyOver argty ->
            BaseRtyUnder
              (L.UnderTy_over_arrow
                 {
                   argname = argname.x;
                   argty;
                   retty = to_under_rty @@ aux body;
                 })
        | BaseRtyUnder argty ->
            let _ =
              try _check_equality __FILE__ __LINE__ String.equal "_" argname.x
              with e ->
                ( MetaEnv.show_debug_info @@ fun _ ->
                  Printf.printf
                    "\n\
                     The unused varaible should use name '_', instead of %s\n\n"
                    argname.x );
                raise e
            in
            BaseRtyUnder
              (L.UnderTy_under_arrow { argty; retty = to_under_rty @@ aux body })
        )
    | Pexp_constraint _ -> baserty_of_ocamlexpr expr
    | _ ->
        _failatwith __FILE__ __LINE__
          (spf "wrong refinement type: %s"
             (Pprintast.string_of_expression expr))
    (* and aux_with_name expr = *)
    (*   match expr.pexp_desc with *)
    (*   | Pexp_apply (x, [ e ]) -> *)
    (*       let ty = aux @@ snd e in *)
    (*       let x = *)
    (*         match Expr.expr_of_ocamlexpr x with *)
    (*         | { x = Var x; _ } -> x *)
    (*         | _ -> _failatwith __FILE__ __LINE__ "" *)
    (*       in *)
    (*       (x, ty) *)
    (*   | _ -> _failatwith __FILE__ __LINE__ "" *)
  in
  let uty = to_under_rty @@ aux expr in
  (* let () = Printf.printf "TEST:%s\n" @@ pretty_layout uty in *)
  uty

let undertype_to_ocamlexpr _ = _failatwith __FILE__ __LINE__ "unimp"
let layout x = Pprintast.string_of_expression @@ undertype_to_ocamlexpr x
