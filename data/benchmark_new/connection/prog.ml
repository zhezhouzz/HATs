type effect =
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

(* tab 0 :: connect: > 0; disconnect: <= 0 *)
(* tab 1 :: content *)

let write (db : nat) (content : int) : unit =
  let (status : int) = perform (Lookup (db, 0)) in
  if status > 0 then
    let (dummy0 : unit) = perform (Update (db, 1, content)) in
    ()
  else ()

let[@assert] write ?l:(db = (true : [%v: nat]))
    ?l:(content = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Update
         ((((v0 == db && v1 == 0 && v2 > 0 : [%v0: nat]) : [%v1: int])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Update
             ((((v0 == db && v1 == 0 : [%v0: nat]) : [%v1: int]) : [%v2: int])
               : [%v: unit])));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        Lookup (((v0 == db && v1 == 0 : [%v0: nat]) : [%v1: int]) : [%v: int]);
        Update
          ((((v0 == db && v1 == 1 && v2 == content : [%v0: nat]) : [%v1: int])
             : [%v2: int])
            : [%v: unit]);
        Ret (true : [%v0: unit])) : unit);
  }

(* let[@assert] reconnect ?l:(a = (true : [%v: unit])) = *)
(*   { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) } *)

(* let[@assert] disconnect ?l:(a = (true : [%v: unit])) = *)
(*   { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) } *)
