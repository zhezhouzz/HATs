type effect =
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

(* Unintialialised < 0 *)
(* Intialialised = 0 *)
(* TaskRunning = 1 *)
(* TaskCompleted = 2 *)
(* HeadersWritten = 3 *)
(* ContentWritten = 4 *)

(* state_tab: 0 *)
(* head_tab: 1 *)
(* content_tab: 2 *)

let write_content (db : nat) (content : int) : unit =
  let (status : int) = perform (Lookup (db, 0)) in
  if status == 3 then
    let (dummy0 : unit) = perform (Update (db, 2, content)) in
    let (dummy1 : unit) = perform (Update (db, 0, 4)) in
    ()
  else ()

let[@assert] write_content ?l:(db = (true : [%v: nat]))
    ?l:(content = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Update
         ((((v0 == db && v1 == 1 : [%v0: nat]) : [%v1: int]) : [%v2: int])
           : [%v: unit]);
       Update
         ((((v0 == db && v1 == 0 && v2 == 3 : [%v0: nat]) : [%v1: int])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Update
             ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit])));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        Update
          ((((v0 == db && v1 == 2 && v2 == content : [%v0: nat]) : [%v1: int])
             : [%v2: int])
            : [%v: unit]);
        Update
          ((((v0 == db && v1 == 0 && v2 == 4 : [%v0: nat]) : [%v1: int])
             : [%v2: int])
            : [%v: unit]);
        Ret (true : [%v0: unit])) : unit);
  }

(* let[@assert] initialise ?l:(a = (true : [%v: unit])) = *)
(*   { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) } *)

(* let[@assert] startTask ?l:(a = (true : [%v: unit])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Initialise (true : [%v0: unit]); *)
(*        starA (NatGen (true : [%v0: unit]))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)

(* let[@assert] finishTask ?l:(a = (true : [%v: unit])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        StartTask (true : [%v0: unit]); *)
(*        starA (NatGen (true : [%v0: unit]))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)

(* let[@assert] writeHeaders ?l:(a = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        FinishTask (true : [%v0: unit]); *)
(*        starA (NatGen (true : [%v0: unit]))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)

(* let[@assert] writeContent ?l:(a = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        WriteHeaders (true : [%v0: int]); *)
(*        starA (NatGen (true : [%v0: unit]))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)
