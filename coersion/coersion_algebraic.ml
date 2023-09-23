open Syntax
open Coersion_lit
module Raw = EquationRaw
open Equation

let rec force_eqterm eqterm =
  match eqterm with
  | Raw.EqtRet e -> EqtRet (force_lit e)
  | Raw.EqtDo { dolhs; effop; effargs; body } ->
      EqtDo { dolhs; effop; effargs; body = force_eqterm body }

let rec besome_eqterm eqterm =
  match eqterm with
  | EqtRet e -> Raw.EqtRet (besome_lit e)
  | EqtDo { dolhs; effop; effargs; body } ->
      Raw.EqtDo { dolhs; effop; effargs; body = besome_eqterm body }

let force_equation equation =
  match equation with
  | Raw.EqObv { elhs; erhs; cond } ->
      EqObv
        {
          elhs = force_eqterm elhs;
          erhs = force_eqterm erhs;
          cond = List.map force_lit cond;
        }
  | Raw.EqState { elhs; erhs } ->
      EqState { elhs = force_eqterm elhs; erhs = force_eqterm erhs }

let besome_equation equation =
  match equation with
  | EqObv { elhs; erhs; cond } ->
      Raw.EqObv
        {
          elhs = besome_eqterm elhs;
          erhs = besome_eqterm erhs;
          cond = List.map besome_lit cond;
        }
  | EqState { elhs; erhs } ->
      Raw.EqState { elhs = besome_eqterm elhs; erhs = besome_eqterm erhs }
