type effect =
  | Write of (int -> unit)
  | Read of (unit -> int)
  | BoolGen of (unit -> bool)

let[@effrty] write ?l:(a = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] read ?l:(a = (true : [%v: unit])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (starA anyA;
       Write (phi v0 : [%v0: int]);
       starA (compA (Write (true : [%v0: int]))));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let[@effrty] boolGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let rec prog (dummy0 : unit) : unit =
  let (cond : bool) = perform (BoolGen ()) in
  if cond then
    let (dummy1 : unit) = perform (Write 0) in
    ()
  else
    let (dummy2 : unit) = prog () in
    let (n : int) = perform (Read ()) in
    let (m : int) = n + 2 in
    let (dummy3 : unit) = perform (Write m) in
    ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre = starA anyA;
    post =
      ((starA anyA;
        Write (v0 mod 2 == 0 : [%v0: int]);
        Ret (true : [%v0: unit])) : unit);
  }