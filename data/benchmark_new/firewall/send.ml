type effect =
  | Write of (int -> unit)
  | Read of (unit -> int)
  | Mem of (nat -> int -> bool)
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

let send (tab : nat) (id : int) : int -> unit =
  let (cid : int) = perform (Read ()) in
  if cid == id then fun (data : int) ->
    let (dummy0 : unit) = perform (Update (tab, id, data)) in
    dummy0
  else if perform (Mem (tab, id)) then
    if perform (Lookup (tab, id)) >= 0 then fun (data : int) ->
      let (dummy1 : unit) = perform (Update (tab, id, data)) in
      dummy1
    else fun (data : int) -> ()
  else fun (data : int) -> ()

let[@assert] send ?l:(tab = (true : [%v: nat])) ?l:(id = (true : [%v: int])) =
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
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit])
          - Write ((true : [%v0: int]) : [%v: unit]));
        (fun ?l:(data = (true : [%v: int])) ->
          {
            pre = starA anyA;
            post =
              ((Update
                  ((((v0 == tab && v1 == id && v2 == data : [%v0: nat])
                      : [%v1: int])
                     : [%v2: int])
                    : [%v: unit]);
                Ret (true : [%v0: unit])) : unit);
          })
        || fun ?l:(data = (true : [%v: int])) ->
        { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }) : int ->
                                                                          unit);
  }
