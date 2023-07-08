type effect =
  | Write of (int -> unit)
  | Read of (unit -> int)
  | Mem of (nat -> int -> bool)
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

let is_device (tab : nat) (id : int) : bool =
  let (cid : int) = perform (Read ()) in
  if cid == id then true
  else if perform (Mem (tab, id)) then
    let (res : int) = perform (Lookup (tab, id)) in
    let (r1 : bool) = res >= 0 in
    r1
  else false

let[@assert] is_device ?l:(tab = (true : [%v: nat]))
    ?l:(id = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Write ((v0 == id : [%v0: int]) : [%v: unit])
       ||
       (Write ((not (v0 == id) : [%v0: int]) : [%v: unit]);
        starA (anyA - Write ((true : [%v0: int]) : [%v: unit])));
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
        Ret (v0 : [%v0: bool])) : bool);
  }

let[@assert] is_device ?l:(tab = (true : [%v: nat]))
    ?l:(id = (true : [%v: int])) =
  {
    pre =
      (starA
         (anyA
         - Update
             ((((v0 == tab && v1 == id : [%v0: nat]) : [%v1: int]) : [%v2: int])
               : [%v: unit]));
       Write ((not (v0 == id) : [%v0: int]) : [%v: unit]);
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
        Ret (not v0 : [%v0: bool])) : bool);
  }

let[@assert] is_device ?l:(tab = (true : [%v: nat]))
    ?l:(id = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Write ((not (v0 == id) : [%v0: int]) : [%v: unit]);
       starA (anyA - Write ((true : [%v0: int]) : [%v: unit]));
       Update
         ((((v0 == tab && v1 == id && v2 < 0 : [%v0: nat]) : [%v1: int])
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
        Ret (not v0 : [%v0: bool])) : bool);
  }
