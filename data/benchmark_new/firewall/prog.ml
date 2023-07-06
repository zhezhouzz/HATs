type effect =
  | Mem of (nat -> int -> bool)
  | Update of (nat -> int -> int -> unit)
  | Lookup of (nat -> int -> int)

(* ctab 0  -> central device *)
(* atab id -> auth *)
(* dtab id -> channel data; where id should greater than 0 *)

(* let send (ctab : nat) (atab : nat) (dtab : nat) (cid : int) (id : int) : *)
(*     int -> unit = *)
(*   let (cid_ : int) = perform (Lookup (ctab, 0)) in *)
(*   if cid == cid_ then *)
(*     if cid == id then *)
(*       let (dummy3 : int) = perform (Lookup (dtab, cid)) in *)
(*       fun (data : int) -> *)
(*         let (dummy0 : unit) = perform (Update (dtab, id, data)) in *)
(*         dummy0 *)
(*     else if perform (Mem (atab, id)) then *)
(*       if perform (Lookup (atab, id)) > 0 then *)
(*         let (dummy4 : int) = perform (Lookup (dtab, cid)) in *)
(*         fun (data : int) -> *)
(*           let (dummy1 : unit) = perform (Update (dtab, id, data)) in *)
(*           dummy1 *)
(*       else fun (data : int) -> () *)
(*     else fun (data : int) -> () *)
(*   else fun (data : int) -> () *)

let send (ctab : nat) (atab : nat) (dtab : nat) (cid : int) (id : int) :
    int -> unit =
  if cid == id then
    let (x : int) = perform (Lookup (dtab, id)) in
    if x > 0 then fun (data : int) ->
      let (dummy0 : unit) = perform (Update (dtab, id, data)) in
      dummy0
    else fun (data : int) -> ()
  else if perform (Lookup (atab, id)) > 0 then
    let (y : int) = perform (Lookup (dtab, cid)) in
    if y > 0 then fun (data : int) ->
      let (dummy1 : unit) = perform (Update (dtab, id, data)) in
      dummy1
    else fun (data : int) -> ()
  else fun (data : int) -> ()

let[@assert] send ?l:(ctab = (true : [%v: nat]))
    ?l:(atab = (not (v == ctab) : [%v: nat]))
    ?l:(dtab = ((not (v == ctab)) && not (v == atab) : [%v: nat]))
    ?l:(cid = (true : [%v: int])) ?l:(id = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Update
         ((((v0 == ctab && v1 == 0 && v2 == cid : [%v0: nat]) : [%v1: int])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Update
             ((((v0 == ctab : [%v0: nat]) : [%v1: int]) : [%v2: int])
               : [%v: unit])));
    post =
      ((starA
          (anyA
          - Update
              ((((true : [%v0: nat]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        (Lookup
           (((v0 == dtab && v1 == cid && v > 0 : [%v0: nat]) : [%v1: int])
             : [%v: int]);
         fun ?l:(data = (true : [%v: int])) ->
           {
             pre =
               (starA anyA;
                Lookup
                  (((v0 == atab && v1 == id && v > 0 : [%v0: nat]) : [%v1: int])
                    : [%v: int]);
                starA
                  (anyA
                  - Update
                      ((((v0 == atab && v1 == id : [%v0: nat]) : [%v1: int])
                         : [%v2: int])
                        : [%v: unit]))
                (* starA anyA *));
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
