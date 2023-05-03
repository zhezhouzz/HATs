open Language
module Nt = Normalty.Ntyped
module R = Rty
open R

type dc = Disj | Conj

let comp a b =
  match (a, b) with
  | Disj, Under -> Disj
  | Disj, Over -> Conj
  | Conj, Under -> Conj
  | Conj, Over -> Disj

let flip = function Disj -> Conj | Conj -> Disj

let merge_base dc { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  let open P in
  let phi2 = P.subst_typed_id (v2, v1) phi2 in
  match dc with
  | Disj -> { v = v1; phi = Or [ phi1; phi2 ] }
  | Conj -> { v = v1; phi = And [ phi1; phi2 ] }

open Sugar

let rec merge_function dc t1 t2 =
  match (t1, t2) with
  | ( Traced { h = h1; pre = pre1; rty = rty1; post = post1 },
      Traced { h = h2; pre = pre2; rty = rty2; post = post2 } ) ->
      let h1 = Nt.(h1 #: (erase_basety pre1)) in
      let h2 = Nt.(h2 #: (erase_basety pre2)) in
      let pre = merge_base dc pre1 pre2 in
      let post2 = subst_basety_id (h2, h1) post2 in
      let post = merge_base dc post1 post2 in
      let rty2 = subst_id (h2, h1) rty2 in
      let rty = merge_function dc rty1 rty2 in
      Traced { h = h1.x; pre; rty; post }
  | Traced { h = h1; pre = pre1; rty = rty1; post = post1 }, _ ->
      Traced
        { h = h1; pre = pre1; rty = merge_function dc rty1 t2; post = post1 }
  | _, Traced { h = h2; pre = pre2; rty = rty2; post = post2 } ->
      Traced
        { h = h2; pre = pre2; rty = merge_function dc t1 rty2; post = post2 }
  | ( BaseRty { ou = ou1; basety = basety1 },
      BaseRty { ou = ou2; basety = basety2 } )
    when ou_eq ou1 ou2 ->
      BaseRty { ou = ou1; basety = merge_base (comp dc ou1) basety1 basety2 }
  | ( DepRty { dep = dep1; label = label1; rarg = rarg1; retrty = retrty1 },
      DepRty { dep = dep2; label = label2; rarg = rarg2; retrty = retrty2 } )
    when dep_eq dep1 dep2 && Leff.eq label1 label2 ->
      let rarg_rty = merge_function (flip dc) rarg1.ty rarg2.ty in
      let retrty2 =
        match (to_ntyped rarg2, to_ntyped rarg1) with
        | Some x2, Some x1 -> subst_id (x2, x1) retrty2
        | None, None -> retrty2
        | _, _ -> _failatwith __FILE__ __LINE__ "?"
      in
      DepRty
        {
          dep = dep1;
          label = label1;
          rarg = rarg1.x #: rarg_rty;
          retrty = merge_function dc retrty1 retrty2;
        }
  | _, _ -> _failatwith __FILE__ __LINE__ "?"

open Zzdatatype.Datatype

let merge = function
  | [] -> _failatwith __FILE__ __LINE__ "?"
  | rty :: rest ->
      let () =
        Pp.printf "@{<bold>%s@} <--merge--\n%s\n" (layout rty)
          (List.split_by "\n" layout rest)
      in
      List.fold_left (merge_function Disj) rty rest
