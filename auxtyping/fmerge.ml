open Language
open Rty
open Sugar

let rec common_sup_unified_pty (t1, t2) =
  match (t1, t2) with
  | BasePty { cty = cty1 }, BasePty { cty = cty2 } ->
      let phi = smart_or [ cty1.phi; cty2.phi ] in
      BasePty { cty = { v = cty1.v; phi } }
  | TuplePty ts1, TuplePty ts2 ->
      let ts =
        List.map common_sup_unified_pty
        @@ _safe_combine __FILE__ __LINE__ ts1 ts2
      in
      TuplePty ts
  | ( ArrPty { arr_kind = PiArr; rarg = rarg1; retrty = retrty1 },
      ArrPty { arr_kind = PiArr; rarg = rarg2; retrty = retrty2 } ) ->
      let rarg = rarg1.px #:: (common_sub_unified_pty (rarg1.pty, rarg2.pty)) in
      let retrty = common_sup_unified_rty (retrty1, retrty2) in
      ArrPty { arr_kind = PiArr; rarg; retrty }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

and common_sup_unified_rty (t1, t2) =
  match (t1, t2) with
  | Pty pty1, Pty pty2 -> Pty (common_sup_unified_pty (pty1, pty2))
  | ( Regty { nty; prereg = pre1; postreg = post1 },
      Regty { prereg = pre2; postreg = post2; _ } ) ->
      let prereg = LandA (pre1, pre2) in
      let postreg = LorA (post1, post2) in
      Regty { nty; prereg; postreg }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

and common_sub_unified_pty (t1, t2) =
  match (t1, t2) with
  | BasePty { cty = cty1 }, BasePty { cty = cty2 } ->
      let phi = smart_and [ cty1.phi; cty2.phi ] in
      BasePty { cty = { v = cty1.v; phi } }
  | TuplePty ts1, TuplePty ts2 ->
      let ts =
        List.map common_sub_unified_pty
        @@ _safe_combine __FILE__ __LINE__ ts1 ts2
      in
      TuplePty ts
  | ( ArrPty { arr_kind = PiArr; rarg = rarg1; retrty = retrty1 },
      ArrPty { arr_kind = PiArr; rarg = rarg2; retrty = retrty2 } ) ->
      let rarg = rarg1.px #:: (common_sup_unified_pty (rarg1.pty, rarg2.pty)) in
      let retrty = common_sub_unified_rty (retrty1, retrty2) in
      ArrPty { arr_kind = PiArr; rarg; retrty }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

and common_sub_unified_rty (t1, t2) =
  match (t1, t2) with
  | Pty pty1, Pty pty2 -> Pty (common_sub_unified_pty (pty1, pty2))
  | ( Regty { nty; prereg = pre1; postreg = post1 },
      Regty { prereg = pre2; postreg = post2; _ } ) ->
      let prereg = LorA (pre1, pre2) in
      let postreg = LandA (post1, post2) in
      Regty { nty; prereg; postreg }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

let common_sub_pty tt = common_sub_unified_pty @@ unify_name_pty tt
let common_sub_rty tt = common_sub_unified_rty @@ unify_name_rty tt
let common_sup_pty tt = common_sup_unified_pty @@ unify_name_pty tt
let common_sup_rty tt = common_sup_unified_rty @@ unify_name_rty tt

open Zzdatatype.Datatype

let multi_merge (f : 'a * 'a -> 'a) (default : unit -> 'a) (l : 'a list) : 'a =
  match l with
  | [] -> default ()
  | rty :: rest -> List.fold_left (fun tau tau' -> f (tau, tau')) rty rest

let common_sub_rtys rtys : rty =
  let () =
    Pp.printf "@{<bold>Disjunction:@}%s\n" (List.split_by ", " layout_rty rtys)
  in
  multi_merge common_sub_rty
    (fun () -> _failatwith __FILE__ __LINE__ "die")
    rtys

(* NOTE: when pos_set (neg_set) is empty, it is equal to the top (bottom) element in the subtyping lattice *)

let common_sub_ptys nty rtys =
  (* let () = *)
  (*   Pp.printf "@{<bold>Disjunction:@}%s\n" (List.split_by ", " layout_pty rtys) *)
  (* in *)
  multi_merge common_sub_pty (fun () -> mk_bot_pty nty) rtys

let common_sup_ptys nty rtys =
  (* let () = *)
  (*   Pp.printf "@{<bold>Conjunction:@}%s\n" (List.split_by ", " layout_pty rtys) *)
  (* in *)
  multi_merge common_sup_pty (fun () -> mk_top_pty nty) rtys
