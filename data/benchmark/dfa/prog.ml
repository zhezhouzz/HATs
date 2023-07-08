type effect =
  | Mem of (nat -> int -> bool)
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

(* There are three tables for a graph *)
(* vtab vid -> \top *)
(* char -> in_id -> out_id *)

let add_edge (vtab : nat) (c : nat) (start_id : int) (end_id : int) : unit =
  if start_id == end_id then ()
  else if perform (Mem (c, start_id)) then ()
  else if perform (Lookup (vtab, start_id)) < 0 then ()
  else
    let (st : int) = perform (Lookup (vtab, end_id)) in
    if st <= 0 then ()
    else
      let (dummy1 : unit) = perform (Update (c, start_id, end_id)) in
      ()

let[@assert] add_edge ?l:(vtab = (true : [%v: nat]))
    ?l:(c = (not (v == vtab) : [%v: nat])) ?l:(start_id = (true : [%v: int]))
    ?l:(end_id = (not (v == start_id) : [%v: int])) =
  {
    pre =
      (starA
         (anyA
         - Update ((c : nat), start_id, ((true : [%v2: int]) : [%v: unit])));
       Update ((vtab : nat), start_id, ((v2 >= 0 : [%v2: int]) : [%v: unit]));
       Update ((vtab : nat), end_id, ((v2 > 0 : [%v2: int]) : [%v: unit]));
       starA
         (anyA
         - Update ((vtab : nat), start_id, ((true : [%v2: int]) : [%v: unit]))
         - Update ((vtab : nat), end_id, ((true : [%v2: int]) : [%v: unit]))
         - Update ((c : nat), start_id, ((true : [%v2: int]) : [%v: unit]))));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        Update ((c : nat), start_id, end_id, (true : [%v: unit]));
        Ret (true : [%v0: unit])) : unit);
  }
