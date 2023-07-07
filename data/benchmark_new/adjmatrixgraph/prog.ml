type effect =
  | Mem of (nat -> int -> bool)
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

(* There are three tables for a graph *)
(* vtab vid -> \top *)
(* in_tab eid -> vid *)
(* out_tab eid -> vid *)

let add_edge (vtab : nat) (etab : nat) (in_tab : nat) (out_tab : nat)
    (eid : int) (start_id : int) (end_id : int) : unit =
  if start_id == end_id then ()
  else if perform (Mem (in_tab, eid)) then ()
  else if perform (Mem (out_tab, eid)) then ()
  else if perform (Mem (vtab, start_id)) then
    if perform (Mem (vtab, end_id)) then
      let (dummy1 : unit) = perform (Update (in_tab, eid, start_id)) in
      let (dummy2 : unit) = perform (Update (out_tab, eid, end_id)) in
      ()
    else ()
  else ()

let[@assert] add_edge ?l:(vtab = (true : [%v: nat]))
    ?l:(etab = (not (v == vtab) : [%v: nat]))
    ?l:(in_tab = ((not (v == vtab)) && not (v == etab) : [%v: nat]))
    ?l:(out_tab =
        ((not (v == vtab)) && (not (v == etab)) && not (v == in_tab)
          : [%v: nat])) ?l:(eid = (true : [%v: int]))
    ?l:(start_id = (true : [%v: int]))
    ?l:(end_id = (not (v == start_id) : [%v: int])) =
  {
    pre =
      (starA
         (anyA
         - Update ((in_tab : nat), eid, ((true : [%v2: int]) : [%v: unit]))
         - Update ((out_tab : nat), eid, ((true : [%v2: int]) : [%v: unit])));
       Update ((vtab : nat), start_id, ((true : [%v2: int]) : [%v: unit]));
       Update ((vtab : nat), end_id, ((true : [%v2: int]) : [%v: unit]));
       starA
         (anyA
         - Update ((vtab : nat), start_id, ((true : [%v2: int]) : [%v: unit]))
         - Update ((vtab : nat), end_id, ((true : [%v2: int]) : [%v: unit]))
         - Update ((in_tab : nat), eid, ((true : [%v2: int]) : [%v: unit]))
         - Update ((out_tab : nat), eid, ((true : [%v2: int]) : [%v: unit]))));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        Update ((in_tab : nat), eid, start_id, (true : [%v: unit]));
        Update ((out_tab : nat), eid, end_id, (true : [%v: unit]));
        Ret (true : [%v0: unit])) : unit);
  }
