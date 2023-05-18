open Language
module PCtx = PTypectx
module Rty = PCtxType
module P = Rty.P
module ECtx = Eqctx
open Rty
open Sugar
open Zzdatatype.Datatype

type pctx = {
  eqctx : ECtx.ctx;
  gamma : PCtx.ctx;
  check : PCtx.ctx -> prop -> bool;
}

let check_prop_valid { gamma; check; _ } phi = check gamma phi

let cond_to_cond_prop eqconds =
  P.(smart_and (List.map (fun lit -> Lit lit) eqconds))

let reduction_none_on_op pctx pre se2 =
  let op2, vs2, phi2 = se_force_op se2 in
  let args2 = List.map (fun x -> find_lit_assignment_from_prop phi2 x) vs2 in
  let res = ECtx.find_none_ret_rules pctx.eqctx (op2, args2) in
  let res =
    List.filter_map
      (fun (res, cond) ->
        let () =
          Printf.printf "res: %s; cond: %s\n" (ECtx.layout_ret_res res)
            (List.split_by_comma layout_lit cond)
        in
        let cond = cond_to_cond_prop cond in
        let prop = smart_and [ pre; cond ] in
        let () =
          Printf.printf "pre: %s; prop: %s\n" (layout_prop pre)
            (layout_prop prop)
        in
        if check_prop_valid pctx prop then Some (prop, res) else None)
      res
  in
  res

let decide_over_seq pctx _ se2 =
  let res = reduction_none_on_op pctx mk_true se2 in
  let props =
    List.fold_left
      (fun props (prop, res) ->
        match res with
        | ECtx.Drop -> _failatwith __FILE__ __LINE__ "die"
        | ECtx.RetResLit _ -> prop :: props)
      [] res
  in
  props

let decide_ret (eqctx : ECtx.ctx) (gamma : PCtx.ctx) check curA se nty =
  let ptcx = { gamma; check; eqctx } in
  let ls = Branching.deseq curA in
  let props = List.concat @@ List.map (fun l -> decide_over_seq ptcx l se) ls in
  let cty = P.{ v = v_name #: nty; phi = smart_or props } in
  BasePty { cty }
