type effect =
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

(* 0: o.cxn: notaliased:>= 0; connected > 0; *)
(* 1: o.site: any *)

let open_page (db : nat) =
  let (site : int) = perform (Lookup (db, 1)) in
  let (dummy0 : unit) = perform (Update (db, 0, 1)) in
  ()

let[@assert] open_page ?l:(db = (true : [%v: nat])) =
  {
    pre =
      (starA anyA;
       Update
         ((((v0 == db && v1 == 1 : [%v0: nat]) : [%v1: int]) : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Update
             ((((v0 == db && v1 == 1 : [%v0: nat]) : [%v1: int]) : [%v2: int])
               : [%v: unit])));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        Update
          ((((v0 == db && v1 == 0 && v2 > 0 : [%v0: nat]) : [%v1: int])
             : [%v2: int])
            : [%v: unit]);
        Ret (true : [%v0: unit])) : unit);
  }

(* let[@assert] closepage ?l:(a = (true : [%v: unit])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Openpage (true : [%v0: unit]); *)
(*        starA (compA (Openpage (true : [%v0: unit])))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)
