type effect = Put of (nat -> nat -> int -> unit) | Get of (nat -> nat -> int)
(* | Mem of (int -> int -> bool) *)
(* | Other of (unit -> unit) *)

(* let[@assert] f1 ?l:(lo = (true : [%v: unit]) [@over]) = *)
(*   { *)
(*     pre = starA anyA; *)
(*     post = *)
(*       ((starA (Other ((true : [%v0: unit]) : [%v1: unit])); *)
(*         Ret (is_none v0 : [%v0: int])) : int); *)
(*   } *)

(* let[@assert] f2 ?l:(lo = (true : [%v: unit]) [@over]) = *)
(*   { *)
(*     pre = starA anyA; *)
(*     post = *)
(*       ((starA (Other ((true : [%v0: unit]) : [%v1: unit])); *)
(*         Ret (is_none v0 : [%v0: int])) : int); *)
(*   } *)

(* let[@assert] f3 ?l:(lo = (true : [%v: unit]) [@over]) = *)
(*   { *)
(*     pre = starA anyA; *)
(*     post = *)
(*       ((starA (Other ((true : [%v0: unit]) : [%v1: unit])); *)
(*         Ret (is_none v0 : [%v0: int])) : int); *)
(*   } *)

let[@effrty] put ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: nat]))
    ?l:(va = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

(* let[@effrty] get ?l:(tab = (true : [%v: int])) ?l:(k = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Mem *)
(*          (((v0 == tab && v1 == k && v : [%v0: int]) : [%v1: int]) : [%v: bool]); *)
(*        starA *)
(*          (anyA *)
(*          - Mem (((v0 == tab && v1 == k : [%v0: int]) : [%v1: int]) : [%v: bool]) *)
(*          )); *)
(*     post = (Ret (true : [%v0: int]) : int); *)
(*   } *)

let[@effrty] get ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: nat])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (starA anyA;
       Put
         ((((v0 == tab && v1 == k && phi v2 : [%v0: nat]) : [%v1: nat])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Put
             ((((v0 == tab && v1 == k : [%v0: nat]) : [%v1: nat]) : [%v2: int])
               : [%v: unit])));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

(* let[@effrty] mem ?l:(tab = (true : [%v: int])) ?l:(k = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Put *)
(*          ((((v0 == tab && v1 == k : [%v0: int]) : [%v1: int]) : [%v2: int]) *)
(*            : [%v: unit]); *)
(*        starA *)
(*          (anyA *)
(*          - Put *)
(*              ((((v0 == tab && v1 == k : [%v0: int]) : [%v1: int]) : [%v2: int]) *)
(*                : [%v: unit]))); *)
(*     post = (Ret (v0 : [%v0: bool]) : bool); *)
(*   } *)

(* let[@effrty] mem ?l:(tab = (true : [%v: int])) ?l:(k = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       starA *)
(*         (anyA *)
(*         - Put *)
(*             ((((v0 == tab && v1 == k : [%v0: int]) : [%v1: int]) : [%v2: int]) *)
(*               : [%v: unit])); *)
(*     post = (Ret (not v0 : [%v0: bool]) : bool); *)
(*   } *)

(* let[@effrty] mem ?l:(tab = (true : [%v: int])) ?l:(k = (true : [%v: int])) = *)
(*   { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) } *)

let prog (auth_tab : nat) (pw_tab : nat) (data_tab : nat) (id : nat) (pw : int)
    : int =
  let (auth_res : int) = perform (Get (auth_tab, id)) in
  if auth_res == 0 then -1
  else
    let (stored_pw : int) = perform (Get (pw_tab, id)) in
    if pw != stored_pw then
      let (dummy0 : unit) = perform (Put (auth_tab, id, 0)) in
      -1
    else
      let (y : int) = perform (Get (data_tab, id)) in
      y

(* let prog (auth_tab : nat) (pw_tab : nat) (data_tab : nat) (id : nat) (pw : int) *)
(*     : int = *)
(*   let (auth_res : int) = perform (Get (auth_tab, id)) in *)
(*   if auth_res == 0 then -1 else -1 *)

let[@assert] prog ?l:(auth_tab = (true : [%v: nat]) [@over])
    ?l:(pw_tab = (not (v == auth_tab) : [%v: nat]) [@over])
    ?l:(data_tab =
        ((not (v == auth_tab)) && not (v == pw_tab) : [%v: nat]) [@over])
    ?l:(id = (true : [%v: nat]) [@over]) ?l:(pw = (true : [%v: int]) [@over]) =
  {
    pre =
      (starA anyA;
       Put
         ((((v0 == pw_tab && v1 == id : [%v0: nat]) : [%v1: nat]) : [%v2: int])
           : [%v: unit]);
       Put
         ((((v0 == data_tab && v1 == id && not (v2 < 0) : [%v0: nat])
             : [%v1: nat])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Put
             ((((v0 == pw_tab && v1 == id : [%v0: nat]) : [%v1: nat])
                : [%v2: int])
               : [%v: unit])
         - Put
             ((((v0 == data_tab && v1 == id : [%v0: nat]) : [%v1: nat])
                : [%v2: int])
               : [%v: unit]));
       Put
         ((((v0 == auth_tab && v1 == id : [%v0: nat]) : [%v1: nat])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Put
             ((((v1 == id : [%v0: nat]) : [%v1: nat]) : [%v2: int])
               : [%v: unit])));
    post =
      ((Get
          (((v0 == auth_tab && v1 == id && v == 0 : [%v0: nat]) : [%v1: nat])
            : [%v: int])
        ||
        (Get
           (((v0 == auth_tab && v1 == id && not (v == 0) : [%v0: nat])
              : [%v1: nat])
             : [%v: int]);
         Get
           (((v0 == pw_tab && v1 == id && not (v == pw) : [%v0: nat])
              : [%v1: nat])
             : [%v: int]);
         Put
           ((((v0 == auth_tab && v1 == id && v2 == 0 : [%v0: nat]) : [%v1: nat])
              : [%v2: int])
             : [%v: unit]));
        Ret (v0 < 0 : [%v0: int]))
       ||
       (Get
          (((v0 == auth_tab && v1 == id && not (v == 0) : [%v0: nat])
             : [%v1: nat])
            : [%v: int]);
        Get
          (((v0 == pw_tab && v1 == id && v == pw : [%v0: nat]) : [%v1: nat])
            : [%v: int]);
        Get
          (((v0 == data_tab && v1 == id && not (v < 0) : [%v0: nat])
             : [%v1: nat])
            : [%v: int]);
        Ret (true : [%v0: int])) : int);
  }
