type effect =
  | Openpage of (unit -> unit)
  | Closepage of (unit -> unit)
  | BoolGen of (unit -> bool)

let[@effrty] openpage ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (starA anyA;
       Closepage (true : [%v0: unit]);
       starA (compA (Closepage (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] closepage ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (starA anyA;
       Openpage (true : [%v0: unit]);
       starA (compA (Openpage (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] boolGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let rec prog (dummy0 : unit) : unit =
  let (cond : bool) = perform (BoolGen ()) in
  if cond then
    let (dummy1 : unit) = perform (Openpage ()) in
    ()
  else
    let (dummy1 : unit) = perform (Openpage ()) in
    let (dummy2 : unit) = perform (Closepage ()) in
    let (dummy3 : unit) = prog () in
    ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre =
      (starA anyA;
       Closepage (true : [%v0: unit]));
    post =
      ((starA anyA;
        Openpage (true : [%v0: unit]);
        Ret (true : [%v0: unit])) : unit);
  }
