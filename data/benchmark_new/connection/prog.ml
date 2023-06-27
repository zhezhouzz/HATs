type effect =
  | Disconnect of (unit -> unit)
  | Reconnect of (unit -> unit)
  | Write of (int -> unit)
  | BoolGen of (unit -> bool)
  | EvenGen of (unit -> int)

let[@effrty] reconnect ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] disconnect ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] write ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Reconnect (true : [%v0: unit]);
       starA (compA (Disconnect (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] boolGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let[@effrty] evenGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (v0 mod 2 == 0 : [%v0: int]) : int) }

let rec prog (dummy0 : unit) : unit =
  let (cond : bool) = perform (BoolGen ()) in
  let (dummy1 : unit) = perform (Reconnect ()) in
  let (n : int) = perform (EvenGen ()) in
  let (dummy2 : unit) = perform (Write n) in
  if cond then
    let (dummy3 : unit) = perform (Disconnect ()) in
    ()
  else
    let (dummy4 : unit) = prog () in
    ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre = starA anyA;
    post =
      ((starA anyA;
        Write (v0 mod 2 == 0 : [%v0: int]);
        Disconnect (true : [%v0: unit]);
        Ret (true : [%v0: unit])) : unit);
  }
