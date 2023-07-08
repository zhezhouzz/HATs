type effect =
  | Write of (int -> unit)
  | Read of (unit -> int)
  | Mem of (nat -> int -> bool)
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

let make_central (tab : nat) (id : int) : unit =
  let (cid : int) = perform (Read ()) in
  if cid == id then ()
  else
    let (dummy0 : unit) = perform (Write id) in
    let (dummy : unit) = perform (Update (tab, id, 0)) in
    ()

let[@assert] make_central ?l:(tab = (true : [%v: nat]))
    ?l:(id = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Write ((not (v0 == id) : [%v0: int]) : [%v: unit]);
       starA (anyA - Write ((true : [%v0: int]) : [%v: unit]));
       Update
         ((((v0 == tab && v1 == id && v2 >= 0 : [%v0: nat]) : [%v1: int])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Write ((true : [%v0: int]) : [%v: unit])
         - Update
             ((((v0 == tab && v1 == id : [%v0: nat]) : [%v1: int]) : [%v2: int])
               : [%v: unit])));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        Write ((v0 == id : [%v0: int]) : [%v: unit]);
        Update
          ((((v0 == tab && v1 == id && v2 == 0 : [%v0: nat]) : [%v1: int])
             : [%v2: int])
            : [%v: unit]);
        Ret (true : [%v0: unit])) : unit);
  }
