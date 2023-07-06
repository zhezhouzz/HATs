type effect =
  (* | Write of (int -> unit) *)
  (* | Read of (unit -> int) *)
  | Mem of (nat -> int -> bool)
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

(* ctab 0  -> central device *)
(* dtab id -> data; where id should greater than 0 *)

let send (ctab : nat) (dtab : nat) (id : int) : int -> unit =
  let (cid : int) = perform (Lookup (ctab, 0)) in
  if cid == id then fun (data : int) ->
    let (dummy0 : unit) = perform (Update (dtab, id, data)) in
    dummy0
  else if perform (Mem (dtab, id)) then
    if perform (Lookup (dtab, id)) >= 0 then fun (data : int) ->
      let (dummy1 : unit) = perform (Update (dtab, id, data)) in
      dummy1
    else fun (data : int) -> ()
  else fun (data : int) -> ()

let[@assert] send ?l:(ctab = (true : [%v: nat]))
    ?l:(dtab = (not (v == ctab) : [%v: nat])) ?l:(id = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       (Update
          ((((v0 == ctab && v1 == 0 && v2 == id : [%v0: nat]) : [%v1: int])
             : [%v2: int])
            : [%v: unit]);
        starA
          (anyA
          - Update
              ((((v0 == ctab && v1 == 0 : [%v0: nat]) : [%v1: int])
                 : [%v2: int])
                : [%v: unit])))
       ||
       (Update
          ((((v0 == ctab && v1 == 0 && not (v2 == id) : [%v0: nat])
              : [%v1: int])
             : [%v2: int])
            : [%v: unit]);
        starA
          (anyA
          - Update
              ((((v0 == ctab && v1 == 0 : [%v0: nat]) : [%v1: int])
                 : [%v2: int])
                : [%v: unit])));
       Update
         ((((v0 == dtab && v1 == id && v2 >= 0 : [%v0: nat]) : [%v1: int])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Update
             ((((v1 == id : [%v0: nat]) : [%v1: int]) : [%v2: int])
               : [%v: unit])));
    post =
      ((Lookup (((v0 == ctab && v1 == 0 : [%v0: nat]) : [%v1: int]) : [%v: int]);
        starA
          (anyA
          - Lookup (((v0 == ctab : [%v0: nat]) : [%v1: int]) : [%v: int])
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        (fun ?l:(data = (true : [%v: int])) ->
          {
            pre = starA anyA;
            post =
              ((Update
                  ((((v0 == dtab && v1 == id && v2 == data : [%v0: nat])
                      : [%v1: int])
                     : [%v2: int])
                    : [%v: unit]);
                Ret (true : [%v0: unit])) : unit);
          })
        || fun ?l:(data = (true : [%v: int])) ->
        { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }) : int ->
                                                                          unit);
  }
