open Syntax
open Coersion_termlang
open Coersion_rty
module Raw = StructureRaw
open Structure

let force_kind = function Raw.RtyLib -> RtyLib | Raw.RtyToCheck -> RtyToCheck
let besome_kind = function RtyLib -> Raw.RtyLib | RtyToCheck -> Raw.RtyToCheck

let force_entry entry =
  match entry with
  (* | Raw.EquationEntry e -> EquationEntry (Coersion_algebraic.force_equation e) *)
  | Raw.Type_dec d -> Type_dec d
  | Raw.Func_dec d -> Func_dec d
  | Raw.FuncImp { name; if_rec; body } ->
      FuncImp { name; if_rec; body = force_typed_term body }
  | Raw.Rty { name; kind; rty } ->
      Rty { name; kind = force_kind kind; rty = force_rty rty }

let besome_entry entry =
  match entry with
  (* | EquationEntry e -> Raw.EquationEntry (Coersion_algebraic.besome_equation e) *)
  | Type_dec d -> Raw.Type_dec d
  | Func_dec d -> Raw.Func_dec d
  | FuncImp { name; if_rec; body } ->
      Raw.FuncImp { name; if_rec; body = besome_typed_term body }
  | Rty { name; kind; rty } ->
      Raw.Rty { name; kind = besome_kind kind; rty = besome_rty rty }

let force_structure st = List.map force_entry st
let besome_structure st = List.map besome_entry st
