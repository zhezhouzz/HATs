type effect =
  | Mem of (nat -> int -> bool)
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

(* There are three tables for a graph *)
(* vtab vid -> \top *)
(* in_tab eid -> vid *)
(* out_tab eid -> vid *)
(* char_tab eid -> int *)

let rec jump (vtab : nat) (etab : nat) (in_tab : nat) (out_tab : nat)
    (char_tab : nat) (start_id : int) (c : int) (eid : int) : int =
  if eid == 0 then -1
  else if perform (Mem (char_tab, eid)) then
    if perform (Lookup (char_tab, eid)) == c then
      if perform (Lookup (in_tab, eid)) == start_id then
        let (res : int) = perform (Lookup (out_tab, eid)) in
        res
      else jump vtab etab in_tab out_tab char_tab start_id c (eid - 1)
    else jump vtab etab in_tab out_tab char_tab start_id c (eid - 1)
  else jump vtab etab in_tab out_tab char_tab start_id c (eid - 1)

let[@assert] jump ?l:(vtab = (true : [%v: nat]))
    ?l:(in_tab = (not (v == vtab) : [%v: nat]))
    ?l:(out_tab = ((not (v == vtab)) && not (v == in_tab) : [%v: nat]))
    ?l:(char_tab =
        ((not (v == vtab)) && (not (v == in_tab)) && not (v == out_tab)
          : [%v: nat])) ?l:(eid = (true : [%v: int]))
    ?l:(start_id = (true : [%v: int])) ?l:(c = (true : [%v: int]))
    ?l:(eid = (true : [%v: int])) =
  {
    pre =
      (starA
         (anyA
         - Update ((in_tab : nat), eid, ((true : [%v2: int]) : [%v: unit]))
         - Update ((out_tab : nat), eid, ((true : [%v2: int]) : [%v: unit]))
         - Update ((char_tab : nat), eid, ((true : [%v2: int]) : [%v: unit])));
       Update ((in_tab : nat), eid, start_id, (true : [%v: unit]));
       Update ((out_tab : nat), eid, ((true : [%v2: int]) : [%v: unit]));
       Update ((char_tab : nat), eid, c, (true : [%v: unit]));
       starA
         (anyA
         - Update ((in_tab : nat), eid, ((true : [%v2: int]) : [%v: unit]))
         - Update ((out_tab : nat), eid, ((true : [%v2: int]) : [%v: unit]))
         - Update ((char_tab : nat), eid, ((true : [%v2: int]) : [%v: unit]))));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        Update ((in_tab : nat), eid, start_id, (true : [%v: unit]));
        Update ((out_tab : nat), eid, end_id, (true : [%v: unit]));
        Ret (true : [%v0: unit])) : unit);
  }
