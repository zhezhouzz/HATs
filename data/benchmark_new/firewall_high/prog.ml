type effect =
  | Write of (nat -> unit)
  | Read of (unit -> nat)
  | Mem of (nat -> bool)
  | Update of (nat -> int -> unit)
  | Lookup of (nat -> int)

let[@effrty] write ?l:(k = (true : [%v: nat])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] read ?l:(u = (true : [%v: unit])) =
  let phi = (true : [%v: nat -> bool]) in
  {
    pre =
      (starA anyA;
       Write ((phi v0 : [%v0: nat]) : [%v: unit]);
       starA (anyA - Write ((true : [%v0: nat]) : [%v: unit])));
    post = (Ret (phi v0 : [%v0: nat]) : nat);
  }

let[@effrty] update ?l:(k = (true : [%v: nat])) ?l:(va = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] lookup ?l:(k = (true : [%v: nat])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (starA anyA;
       Update (((v0 == k && phi v2 : [%v0: nat]) : [%v2: int]) : [%v: unit]);
       starA (anyA - Update (((v0 == k : [%v0: nat]) : [%v2: int]) : [%v: unit])));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let[@effrty] mem ?l:(k = (true : [%v: nat])) =
  {
    pre =
      (starA anyA;
       Update (((v0 == k : [%v0: nat]) : [%v2: int]) : [%v: unit]);
       starA (anyA - Update (((v0 == k : [%v0: nat]) : [%v2: int]) : [%v: unit])));
    post = (Ret (v0 : [%v0: bool]) : bool);
  }

let[@effrty] mem ?l:(k = (true : [%v: nat])) =
  {
    pre =
      starA (anyA - Update (((v0 == k : [%v0: nat]) : [%v2: int]) : [%v: unit]));
    post = (Ret (not v0 : [%v0: bool]) : bool);
  }

let send (id : nat) : int -> unit =
  let (cid : nat) = perform (Read ()) in
  if eqn cid id then fun (data : int) ->
    let (dummy0 : unit) = perform (Update (id, data)) in
    dummy0
  else if perform (Mem id) then
    if perform (Lookup id) >= 0 then fun (data : int) ->
      let (dummy1 : unit) = perform (Update (id, data)) in
      dummy1
    else fun (data : int) -> ()
  else fun (data : int) -> ()

let[@assert] send ?l:(id = (true : [%v: nat])) =
  {
    pre =
      (starA anyA;
       Write ((v0 == id : [%v0: nat]) : [%v: unit])
       ||
       (Write ((not (v0 == id) : [%v0: nat]) : [%v: unit]);
        starA (anyA - Write ((true : [%v0: nat]) : [%v: unit])));
       Update (((v0 == id && v2 >= 0 : [%v0: nat]) : [%v2: int]) : [%v: unit]);
       starA
         (anyA
         - Write ((true : [%v0: nat]) : [%v: unit])
         - Update (((v0 == id : [%v0: nat]) : [%v2: int]) : [%v: unit])));
    post =
      ((starA
          (anyA
          - Update (((true : [%v0: nat]) : [%v2: int]) : [%v: unit])
          - Write ((true : [%v0: nat]) : [%v: unit]));
        (fun ?l:(data = (true : [%v: int])) ->
          {
            pre = starA anyA;
            post =
              ((Update
                  (((v0 == id && v1 == data : [%v0: nat]) : [%v1: int])
                    : [%v: unit]);
                Ret (true : [%v0: unit])) : unit);
          })
        || fun ?l:(data = (true : [%v: int])) ->
        { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }) : int ->
                                                                          unit);
  }

(* let[@assert] send ?l:(id = (true : [%v: nat])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Write ((v0 == id : [%v0: nat]) : [%v: unit]); *)
(*        starA (anyA - Write ((true : [%v0: nat]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA *)
(*           (anyA *)
(*           - Update (((true : [%v0: nat]) : [%v2: int]) : [%v: unit]) *)
(*           - Write ((true : [%v0: nat]) : [%v: unit])); *)
(*         (fun ?l:(data = (true : [%v: int])) -> *)
(*           { *)
(*             pre = starA anyA; *)
(*             post = *)
(*               ((Update *)
(*                   (((v0 == id && v1 == data : [%v0: nat]) : [%v1: int]) *)
(*                     : [%v: unit]); *)
(*                 Ret (true : [%v0: unit])) : unit); *)
(*           }) *)
(*         || fun ?l:(data = (true : [%v: int])) -> *)
(*         { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }) : int -> *)
(*                                                                           unit); *)
(*   } *)

(* let is_device (id : nat) : unit -> bool = *)
(*   let (cid : nat) = perform (Read ()) in *)
(*   if cid == id then fun (dummy0 : unit) -> true *)
(*   else fun (dummy1 : unit) -> *)
(*     if perform (Mem id) then *)
(*       let (res : int) = perform (Lookup id) in *)
(*       let (r1 : bool) = res >= 0 in *)
(*       r1 *)
(*     else false *)

(* let[@assert] is_device ?l:(a = (true : [%v: nat])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Update (((v0 == a && v1 >= 0 : [%v0: nat]) : [%v1: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == a : [%v0: nat]) : [%v1: int]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA (anyA - Update (((true : [%v0: nat]) : [%v1: int]) : [%v: unit])); *)
(*         Ret (v0 : [%v0: bool])) : bool); *)
(*   } *)

(* let[@assert] is_device ?l:(a = (true : [%v: nat])) = *)
(*   { *)
(*     pre = *)
(*       starA (anyA - Update (((v0 == a : [%v0: nat]) : [%v1: int]) : [%v: unit])) *)
(*       || *)
(*       (starA anyA; *)
(*        Update (((v0 == a && v1 < 0 : [%v0: nat]) : [%v1: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == a : [%v0: nat]) : [%v1: int]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA (anyA - Update (((true : [%v0: nat]) : [%v1: int]) : [%v: unit])); *)
(*         Ret (not v0 : [%v0: bool])) : bool); *)
(*   } *)

(* let add_device (id : nat) : unit = *)
(*   let (res : int) = perform (Lookup id) in *)
(*   if res >= 0 then () *)
(*   else *)
(*     let (dummy0 : unit) = perform (Update (id, 1)) in *)
(*     dummy0 *)

(* let[@assert] add_device ?l:(a = (true : [%v: nat])) = *)
(*   { *)
(*     pre = *)
(*       starA (anyA - Update (((v0 == a : [%v0: nat]) : [%v1: int]) : [%v: unit])) *)
(*       || *)
(*       (starA anyA; *)
(*        Update (((v0 == a && v1 < 0 : [%v0: nat]) : [%v1: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == a : [%v0: nat]) : [%v1: int]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA (anyA - Update (((true : [%v0: nat]) : [%v1: int]) : [%v: unit])); *)
(*         Update (((v0 == a && v1 > 0 : [%v0: nat]) : [%v1: int]) : [%v: unit]); *)
(*         Ret (true : [%v0: unit])) : unit); *)
(*   } *)

(* let delete_device (id : nat) : unit = *)
(*   let (res : int) = perform (Lookup id) in *)
(*   if res == 0 then () *)
(*   else *)
(*     let (dummy0 : unit) = perform (Update (id, -1)) in *)
(*     dummy0 *)

(* let[@assert] delete_device ?l:(a = (true : [%v: nat])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Update (((v0 == a && v1 > 0 : [%v0: nat]) : [%v1: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == a : [%v0: nat]) : [%v1: int]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA (anyA - Update (((true : [%v0: nat]) : [%v1: int]) : [%v: unit])); *)
(*         Update (((v0 == a && v1 < 0 : [%v0: nat]) : [%v1: int]) : [%v: unit]); *)
(*         Ret (true : [%v0: unit])) : unit); *)
(*   } *)

(* let make_central (id : nat) : unit = *)
(*   let (res : int) = perform (Lookup id) in *)
(*   if res < 0 then () *)
(*   else *)
(*     let (dummy0 : unit) = perform (Update (id, 0)) in *)
(*     dummy0 *)

(* let[@assert] make_central ?l:(a = (true : [%v: nat])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Update (((v0 == a && v1 >= 0 : [%v0: nat]) : [%v1: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == a : [%v0: nat]) : [%v1: int]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA (anyA - Update (((true : [%v0: nat]) : [%v1: int]) : [%v: unit])); *)
(*         Update (((v0 == a && v1 == 0 : [%v0: nat]) : [%v1: int]) : [%v: unit]); *)
(*         Ret (true : [%v0: unit])) : unit); *)
(*   } *)
