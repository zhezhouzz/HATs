type effect =
  | Lock of (unit -> unit)
  | Unlock of (unit -> unit)
  | BoolGen of (unit -> bool)

let[@effrty] lock ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (starA anyA;
       Unlock (true : [%v0: unit]);
       starA (compA (Unlock (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] unlock ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (starA anyA;
       Lock (true : [%v0: unit]);
       starA (compA (Lock (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] boolGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let rec prog (dummy0 : unit) : unit =
  let (cond : bool) = perform (BoolGen ()) in
  if cond then
    let (dummy1 : unit) = perform (Lock ()) in
    ()
  else
    let (dummy1 : unit) = perform (Lock ()) in
    let (dummy2 : unit) = perform (Unlock ()) in
    let (dummy3 : unit) = prog () in
    ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre =
      (starA anyA;
       Unlock (true : [%v0: unit]));
    post =
      ((starA anyA;
        Lock (true : [%v0: unit]);
        Ret (true : [%v0: unit])) : unit);
  }
