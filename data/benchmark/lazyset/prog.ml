type effect = Setinsert of (int -> unit) | Setmem of (int -> bool)

(* A set equips with a min and max *)

let lazy_insert (thunk : unit -> unit) (elem : int) : unit -> unit =
  if perform (Setmem elem) then fun (x : unit) ->
    let (dummy1 : unit) = thunk () in
    ()
  else fun (x : unit) ->
    let (dummy1 : unit) = thunk () in
    let (dummy2 : unit) = perform (Setinsert elem) in
    ()

let[@assert] lazy_insert
    ?l:(thunk =
        fun ?l:(x = (true : [%v: unit])) ->
          {
            pre = starA anyA;
            post =
              ((starA (Setinsert ((true : [%v1: int]) : [%v: unit]));
                Ret (true : [%v0: unit])) : unit);
          }) ?l:(elem = (true : [%v: int])) =
  {
    pre = starA anyA;
    post =
      ((starA (anyA - Setinsert ((true : [%v0: int]) : [%v: unit]));
        (Setmem (elem, (v : [%v: bool]));
         Ret
           (fun ?l:(x = (true : [%v: unit])) ->
             {
               pre = starA anyA;
               post =
                 ((starA (Setinsert ((true : [%v1: int]) : [%v: unit]));
                   Ret (true : [%v0: unit])) : unit);
             }))
        ||
        (Setmem (elem, (not v : [%v: bool]));
         Ret
           (fun ?l:(x = (true : [%v: unit])) ->
             {
               pre = starA anyA;
               post =
                 ((starA (Setinsert ((true : [%v1: int]) : [%v: unit]));
                   Setinsert (elem, (true : [%v: unit]));
                   Ret (true : [%v0: unit])) : unit);
             }))) : unit -> unit);
  }
