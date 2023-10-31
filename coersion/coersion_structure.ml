open Syntax
open Coersion_termlang
open Coersion_rty
module Raw = StructureRaw
open Structure

let force_kind = function Raw.RtyLib -> RtyLib | Raw.RtyToCheck -> RtyToCheck
let besome_kind = function RtyLib -> Raw.RtyLib | RtyToCheck -> Raw.RtyToCheck

open Sugar

let force_entry entry =
  match entry with
  | Raw.Type_dec d -> Type_dec d
  | Raw.Func_dec d -> Func_dec d
  | Raw.FuncImp { name; if_rec; body } ->
      FuncImp { name; if_rec; body = force_typed_term body }
  | Raw.Rty { name; kind; rty } ->
      Rty { name; kind = force_kind kind; rty = force_rty rty }
  | Raw.SrlPred { name; args; srl_body } ->
      SrlPred { name; args; srl_body = Coersion_srl.force srl_body }
  | Raw.LtlfRty _ -> _failatwith __FILE__ __LINE__ "die"
  | Raw.LtlfPred _ -> _failatwith __FILE__ __LINE__ "die"
  | Raw.(Axiom { name; uninterops; body }) ->
      Axiom { name; uninterops; body = Coersion_qualifier.force body }

let besome_entry entry =
  match entry with
  | Type_dec d -> Raw.Type_dec d
  | Func_dec d -> Raw.Func_dec d
  | FuncImp { name; if_rec; body } ->
      Raw.FuncImp { name; if_rec; body = besome_typed_term body }
  | Rty { name; kind; rty } ->
      Raw.Rty { name; kind = besome_kind kind; rty = besome_rty rty }
  | SrlPred { name; args; srl_body } ->
      Raw.SrlPred { name; args; srl_body = Coersion_srl.besome srl_body }
  | Axiom { name; uninterops; body } ->
      Raw.Axiom { name; uninterops; body = Coersion_qualifier.besome body }
  | LtlfPred _ -> _failatwith __FILE__ __LINE__ "die"
  | LtlfRty _ -> _failatwith __FILE__ __LINE__ "die"

let force_structure st = List.map force_entry st
let besome_structure st = List.map besome_entry st
