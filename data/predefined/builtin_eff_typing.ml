let[@effrty] boolGen ?l:(k = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let[@effrty] write ?l:(k = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] read ?l:(u = (true : [%v: unit])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (starA anyA;
       Write ((phi v0 : [%v0: int]) : [%v: unit]);
       starA (anyA - Write ((true : [%v0: int]) : [%v: unit])));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

(* let[@effrty] update ?l:(k = (true : [%v: int])) ?l:(va = (true : [%v: int])) = *)
(*   { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) } *)

(* let[@effrty] lookup ?l:(k = (true : [%v: int])) = *)
(*   let phi = (true : [%v: int -> bool]) in *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Update (((v0 == k && phi v2 : [%v0: int]) : [%v2: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == k : [%v0: int]) : [%v2: int]) : [%v: unit]))); *)
(*     post = (Ret (phi v0 : [%v0: int]) : int); *)
(*   } *)

(* let[@effrty] mem ?l:(k = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Update (((v0 == k : [%v0: int]) : [%v2: int]) : [%v: unit]); *)
(*        starA (anyA - Update (((v0 == k : [%v0: int]) : [%v2: int]) : [%v: unit]))); *)
(*     post = (Ret (v0 : [%v0: bool]) : bool); *)
(*   } *)

(* let[@effrty] mem ?l:(k = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       starA (anyA - Update (((v0 == k : [%v0: int]) : [%v2: int]) : [%v: unit])); *)
(*     post = (Ret (not v0 : [%v0: bool]) : bool); *)
(*   } *)

let[@effrty] update ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: int]))
    ?l:(va = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

(* let[@effrty] lookup ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: int])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        Mem *)
(*          (((v0 == tab && v1 == k && v : [%v0: nat]) : [%v1: int]) : [%v: bool])); *)
(*     post = (Ret (true : [%v0: int]) : int); *)
(*   } *)

let[@effrty] lookup ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: int]) : int) }

let[@effrty] lookup ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: int])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (starA anyA;
       Update
         ((((v0 == tab && v1 == k && phi v2 : [%v0: nat]) : [%v1: int])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Update
             ((((v0 == tab && v1 == k : [%v0: nat]) : [%v1: int]) : [%v2: int])
               : [%v: unit])));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let[@effrty] mem ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let[@effrty] mem ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Update
         ((((v0 == tab && v1 == k : [%v0: nat]) : [%v1: int]) : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Update
             ((((v0 == tab && v1 == k : [%v0: nat]) : [%v1: int]) : [%v2: int])
               : [%v: unit])));
    post = (Ret (v0 : [%v0: bool]) : bool);
  }

let[@effrty] mem ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: int])) =
  {
    pre =
      starA
        (anyA
        - Update
            ((((v0 == tab && v1 == k : [%v0: nat]) : [%v1: int]) : [%v2: int])
              : [%v: unit]));
    post = (Ret (not v0 : [%v0: bool]) : bool);
  }

let[@effrty] put ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: nat]))
    ?l:(va = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

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

let[@effrty] exists ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: nat])) =
  {
    pre =
      (starA anyA;
       Put
         ((((v0 == tab && v1 == k : [%v0: nat]) : [%v1: nat]) : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Put
             ((((v0 == tab && v1 == k : [%v0: nat]) : [%v1: nat]) : [%v2: int])
               : [%v: unit])));
    post = (Ret (v0 : [%v0: bool]) : bool);
  }

let[@effrty] exists ?l:(tab = (true : [%v: nat])) ?l:(k = (true : [%v: nat])) =
  {
    pre =
      starA
        (anyA
        - Put
            ((((v0 == tab && v1 == k : [%v0: nat]) : [%v1: nat]) : [%v2: int])
              : [%v: unit]));
    post = (Ret (not v0 : [%v0: bool]) : bool);
  }
