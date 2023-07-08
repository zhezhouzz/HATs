type effect =
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)
  | Mem of (nat -> int -> bool)
  | BoolGen of (unit -> bool)

(* open db may fail *)

(* Unintialialised < 0 *)
(* SQLiteConnected = 0 *)
(* SQLitePS Binding = 1 *)
(* SQLitePS Bound = 2 *)

let open_db (sqlite : nat) (db_id : int) : bool =
  if perform (Mem (sqlite, db_id)) then
    let (status : int) = perform (Lookup (sqlite, db_id)) in
    if status < 0 then
      let (dummy0 : unit) = perform (Update (sqlite, db_id, 0)) in
      true
    else false
  else if perform (BoolGen ()) then
    let (dummy0 : unit) = perform (Update (sqlite, db_id, 0)) in
    true
  else false

let[@assert] open_db ?l:(sqlite = (true : [%v: nat]))
    ?l:(db_int = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Update
         ((((v0 == sqlite && v1 == db_int && v2 < 0 : [%v0: nat]) : [%v1: int])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Update
             ((((v0 == sqlite && v1 == db_int : [%v0: nat]) : [%v1: int])
                : [%v2: int])
               : [%v: unit])));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        (Update
           ((((v0 == sqlite && v1 == db_int && v2 == 0 : [%v0: nat])
               : [%v1: int])
              : [%v2: int])
             : [%v: unit]);
         Ret (v0 : [%v0: bool]))
        || Ret (not v0 : [%v0: bool])) : bool);
  }

(* let[@assert] open_db ?l:(sqlite = (true : [%v: nat])) *)
(*     ?l:(db_int = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       starA *)
(*         (anyA *)
(*         - Update *)
(*             ((((v0 == sqlite && v1 == db_int : [%v0: nat]) : [%v1: int]) *)
(*                : [%v2: int]) *)
(*               : [%v: unit])); *)
(*     post = *)
(*       ((starA *)
(*           (anyA *)
(*           - Update *)
(*               ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit])); *)
(*         (Update *)
(*            ((((v0 == sqlite && v1 == db_int && v2 == 0 : [%v0: nat]) *)
(*                : [%v1: int]) *)
(*               : [%v2: int]) *)
(*              : [%v: unit]); *)
(*          Ret (v0 : [%v0: bool])) *)
(*         || Ret (not v0 : [%v0: bool])) : bool); *)
(*   } *)

(* let[@assert] openDB ?l:(a = (true : [%v: unit])) = *)
(*   { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) } *)

let close_db (sqlite : nat) (db_id : int) : unit =
  if perform (Mem (sqlite, db_id)) then
    let (status : int) = perform (Lookup (sqlite, db_id)) in
    if status == 0 then
      let (dummy0 : unit) = perform (Update (sqlite, db_id, -1)) in
      ()
    else ()
  else ()

(* let[@assert] closeDB ?l:(a = (true : [%v: unit])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        OpenDB (true : [%v0: unit]); *)
(*        starA (compA (CloseDB (true : [%v0: unit])))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)

let prepare_statement (sqlite : nat) (db_id : int) : bool =
  if perform (Mem (sqlite, db_id)) then
    let (status : int) = perform (Lookup (sqlite, db_id)) in
    if status == 0 then
      if perform (BoolGen ()) then
        let (dummy0 : unit) = perform (Update (sqlite, db_id, 1)) in
        true
      else false
    else false
  else false

(* let[@assert] prepareStatement ?l:(a = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        OpenDB (true : [%v0: unit]); *)
(*        starA (compA (CloseDB (true : [%v0: unit])))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)

let finish_bind (sqlite : nat) (db_id : int) : bool =
  if perform (Mem (sqlite, db_id)) then
    let (status : int) = perform (Lookup (sqlite, db_id)) in
    if status == 1 then
      if perform (BoolGen ()) then
        let (dummy0 : unit) = perform (Update (sqlite, db_id, 2)) in
        true
      else
        let (dummy0 : unit) = perform (Update (sqlite, db_id, 0)) in
        false
    else false
  else false

(* let[@assert] finishBind ?l:(a = (true : [%v: unit])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        PrepareStatement (true : [%v0: int]); *)
(*        starA (compA (FinishBind (true : [%v0: unit])))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)

let execute_statement (sqlite : nat) (db_id : int) : bool =
  if perform (Mem (sqlite, db_id)) then
    let (status : int) = perform (Lookup (sqlite, db_id)) in
    if status == 2 then
      if perform (BoolGen ()) then
        let (dummy0 : unit) = perform (Update (sqlite, db_id, 2)) in
        true
      else
        let (dummy0 : unit) = perform (Update (sqlite, db_id, 0)) in
        false
    else false
  else false

(* let[@assert] executeStatement ?l:(a = (true : [%v: unit])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        FinishBind (true : [%v0: unit]); *)
(*        starA (compA (CloseDB (true : [%v0: unit])))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)
