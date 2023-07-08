type effect =
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)
  | Mem of (nat -> int -> bool)

let add_file_or_dir (p1 : nat) (p2 : int) : unit =
  if p2 == 0 then
    let (dummy0 : unit) = perform (Update (p1, p2, 0)) in
    ()
  else if perform (Mem (p1, 0)) then
    let (dummy0 : unit) = perform (Update (p1, p2, 0)) in
    ()
  else ()

let[@assert] add_file_or_dir ?l:(p1 = (true : [%v: nat]))
    ?l:(p2 = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Update
         ((((v0 == p1 && v1 == 0 : [%v0: nat]) : [%v1: int]) : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Update
             ((((v0 == p1 && v1 == p2 : [%v0: nat]) : [%v1: int]) : [%v2: int])
               : [%v: unit])));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        Update
          ((((v0 == p1 && v1 == p2 : [%v0: nat]) : [%v1: int]) : [%v2: int])
            : [%v: unit]);
        Ret (true : [%v0: unit])) : unit);
  }
