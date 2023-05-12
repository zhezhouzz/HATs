open Language
open Rty
open Sugar

let rec conj_unified_pty (t1, t2) =
  match (t1, t2) with
  | BasePty { ou; cty = cty1 }, BasePty { cty = cty2; _ } ->
      let phi =
        match ou with
        | Under -> smart_and [ cty1.phi; cty2.phi ]
        | Over -> smart_or [ cty1.phi; cty2.phi ]
      in
      BasePty { ou; cty = { v = cty1.v; phi } }
  | TuplePty ts1, TuplePty ts2 ->
      let ts =
        List.map conj_unified_pty @@ _safe_combine __FILE__ __LINE__ ts1 ts2
      in
      TuplePty ts
  | ( ArrPty { rarg = rarg1; retrty = retrty1 },
      ArrPty { rarg = rarg2; retrty = retrty2 } ) ->
      let rarg = rarg1.px #:: (disj_unified_pty (rarg1.pty, rarg2.pty)) in
      let retrty = conj_unified_rty (retrty1, retrty2) in
      ArrPty { rarg; retrty }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

and conj_unified_rty (t1, t2) =
  match (t1, t2) with
  | Pty pty1, Pty pty2 -> Pty (conj_unified_pty (pty1, pty2))
  | Regty regex1, Regty regex2 ->
      Regty Nt.{ x = LandA (regex1.x, regex2.x); ty = regex1.ty }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

and disj_unified_pty (t1, t2) =
  match (t1, t2) with
  | BasePty { ou; cty = cty1 }, BasePty { cty = cty2; _ } ->
      let phi =
        match ou with
        | Under -> smart_or [ cty1.phi; cty2.phi ]
        | Over -> smart_and [ cty1.phi; cty2.phi ]
      in
      BasePty { ou; cty = { v = cty1.v; phi } }
  | TuplePty ts1, TuplePty ts2 ->
      let ts =
        List.map disj_unified_pty @@ _safe_combine __FILE__ __LINE__ ts1 ts2
      in
      TuplePty ts
  | ( ArrPty { rarg = rarg1; retrty = retrty1 },
      ArrPty { rarg = rarg2; retrty = retrty2 } ) ->
      let rarg = rarg1.px #:: (conj_unified_pty (rarg1.pty, rarg2.pty)) in
      let retrty = disj_unified_rty (retrty1, retrty2) in
      ArrPty { rarg; retrty }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

and disj_unified_rty (t1, t2) =
  match (t1, t2) with
  | Pty pty1, Pty pty2 -> Pty (disj_unified_pty (pty1, pty2))
  | Regty regex1, Regty regex2 ->
      Regty Nt.{ x = LorA (regex1.x, regex2.x); ty = regex1.ty }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

let disj_pty tt = disj_unified_pty @@ unify_name_pty tt
let disj_rty tt = disj_unified_rty @@ unify_name_rty tt
let conj_pty tt = conj_unified_pty @@ unify_name_pty tt
let conj_rty tt = conj_unified_rty @@ unify_name_rty tt

open Zzdatatype.Datatype

let multi_merge (f : 'a * 'a -> 'a) (l : 'a list) : 'a =
  match l with
  | [] -> _failatwith __FILE__ __LINE__ "?"
  | rty :: rest -> List.fold_left (fun tau tau' -> f (tau, tau')) rty rest

let disj_rtys rtys : t =
  let () =
    Pp.printf "@{<bold>Disjunction:@}%s\n" (List.split_by ", " layout rtys)
  in
  multi_merge disj_rty rtys

let disj_ptys rtys =
  (* let () = *)
  (*   Pp.printf "@{<bold>Disjunction:@}%s\n" (List.split_by ", " layout_pty rtys) *)
  (* in *)
  multi_merge disj_pty rtys

let conj_ptys rtys =
  (* let () = *)
  (*   Pp.printf "@{<bold>Conjunction:@}%s\n" (List.split_by ", " layout_pty rtys) *)
  (* in *)
  multi_merge conj_pty rtys
