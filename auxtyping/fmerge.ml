open Language
open Rty

type dc = Disj | Conj

let unify_cty { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  let open P in
  let phi2 = subst_prop_id (v2.x, v1.x) phi2 in
  (v1, [ phi1; phi2 ])

open Sugar

let rec merge_pty t1 t2 =
  match (t1, t2) with
  | BasePty { ou = Over; cty = cty1 }, BasePty { ou = Over; cty = cty2 } ->
      let v, phis = unify_cty cty1 cty2 in
      BasePty { ou = Over; cty = { v; phi = smart_and phis } }
  | BasePty { ou = Under; cty = cty1 }, BasePty { ou = Under; cty = cty2 } ->
      let v, phis = unify_cty cty1 cty2 in
      BasePty { ou = Under; cty = { v; phi = smart_or phis } }
  | ( ArrPty { rarg = rarg1; retrty = retrty1 },
      ArrPty { rarg = rarg2; retrty = retrty2 } ) ->
      let pty = merge_pty rarg1.pty rarg2.pty in
      let retrty2 =
        match (rarg2.px, rarg1.px) with
        | Some x2, Some x1 -> subst_id (x2, x1) retrty2
        | None, None -> retrty2
        | _, _ -> _failatwith __FILE__ __LINE__ "?"
      in
      ArrPty { rarg = rarg1.px #:: pty; retrty = merge_rty retrty1 retrty2 }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

and merge_rty t1 t2 =
  match (t1, t2) with
  | Pty pty1, Pty pty2 -> Pty (merge_pty pty1 pty2)
  | Regty regex1, Regty regex2 ->
      Regty Nt.{ x = merge_regex regex1.x regex2.x; ty = regex1.ty }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

and merge_regex regex1 regex2 = LorA (regex1, regex2)

open Zzdatatype.Datatype

let merge_rtys = function
  | [] -> _failatwith __FILE__ __LINE__ "?"
  | rty :: rest ->
      let () =
        Pp.printf "@{<bold>%s@} <--merge--\n%s\n" (layout rty)
          (List.split_by "\n" layout rest)
      in
      List.fold_left merge_rty rty rest
