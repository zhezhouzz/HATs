type effect =
  | Update of (nat -> nat -> unit)
  | Lookup of (nat -> nat)
  | Mem of (int -> nat -> bool)
  | Put of (int -> nat -> int -> unit)
  | Get of (int -> nat -> int)

let[@effrty] put ?l:(tab = (true : [%v: int])) ?l:(k = (true : [%v: nat]))
    ?l:(va = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] get ?l:(tab = (true : [%v: int])) ?l:(k = (true : [%v: nat])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (starA anyA;
       Put
         ((((v0 == tab && v1 == k && phi v2 : [%v0: int]) : [%v1: nat])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Put
             ((((v0 == tab && v1 == k : [%v0: int]) : [%v1: nat]) : [%v2: int])
               : [%v: unit])));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let[@effrty] mem ?l:(tab = (true : [%v: int])) ?l:(k = (true : [%v: nat])) =
  {
    pre =
      (starA anyA;
       Put
         ((((v0 == tab && v1 == k : [%v0: int]) : [%v1: nat]) : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Put
             ((((v0 == tab && v1 == k : [%v0: int]) : [%v1: nat]) : [%v2: int])
               : [%v: unit])));
    post = (Ret (v0 : [%v0: bool]) : bool);
  }

let[@effrty] mem ?l:(tab = (true : [%v: int])) ?l:(k = (true : [%v: nat])) =
  {
    pre =
      starA
        (anyA
        - Put
            ((((v0 == tab && v1 == k : [%v0: int]) : [%v1: nat]) : [%v2: int])
              : [%v: unit]));
    post = (Ret (not v0 : [%v0: bool]) : bool);
  }

let is_device (cid : nat) : nat -> bool =
  let (tab : nat) = perform (Lookup cid) in
  fun (id : nat) ->
    if id == cid then true
    else
      let (res : int) = perform (Get (tab, id)) in
      let (is_d : bool) = res > 0 in
      is_d

let[@assert] is_device ?l:(a = (true : [%v: nat])) =
  {
    pre =
      (starA anyA;
       Update (((v0 == a && v1 >= 0 : [%v0: int]) : [%v1: int]) : [%v: unit]);
       starA (anyA - Update (((v0 == a : [%v0: int]) : [%v1: int]) : [%v: unit])));
    post =
      ((starA (anyA - Update (((true : [%v0: int]) : [%v1: int]) : [%v: unit]));
        Ret (v0 : [%v0: bool])) : bool);
  }

(* let[@assert] is_device ?l:(a = (true : [%v: nat])) = *)
(*   { *)
(*     pre = *)
(*       starA (anyA - Update (((v0 == a : [%v0: int]) : [%v1: int]) : [%v: unit])) *)
(*       || *)
(*       (starA anyA; *)
(*        Update (((v0 == a && v1 < 0 : [%v0: int]) : [%v1: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == a : [%v0: int]) : [%v1: int]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA (anyA - Update (((true : [%v0: int]) : [%v1: int]) : [%v: unit])); *)
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
(*       starA (anyA - Update (((v0 == a : [%v0: int]) : [%v1: int]) : [%v: unit])) *)
(*       || *)
(*       (starA anyA; *)
(*        Update (((v0 == a && v1 < 0 : [%v0: int]) : [%v1: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == a : [%v0: int]) : [%v1: int]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA (anyA - Update (((true : [%v0: int]) : [%v1: int]) : [%v: unit])); *)
(*         Update (((v0 == a && v1 > 0 : [%v0: int]) : [%v1: int]) : [%v: unit]); *)
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
(*        Update (((v0 == a && v1 > 0 : [%v0: int]) : [%v1: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == a : [%v0: int]) : [%v1: int]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA (anyA - Update (((true : [%v0: int]) : [%v1: int]) : [%v: unit])); *)
(*         Update (((v0 == a && v1 < 0 : [%v0: int]) : [%v1: int]) : [%v: unit]); *)
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
(*        Update (((v0 == a && v1 >= 0 : [%v0: int]) : [%v1: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == a : [%v0: int]) : [%v1: int]) : [%v: unit]))); *)
(*     post = *)
(*       ((starA (anyA - Update (((true : [%v0: int]) : [%v1: int]) : [%v: unit])); *)
(*         Update (((v0 == a && v1 == 0 : [%v0: int]) : [%v1: int]) : [%v: unit]); *)
(*         Ret (true : [%v0: unit])) : unit); *)
(*   } *)
