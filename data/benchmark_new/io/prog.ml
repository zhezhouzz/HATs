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
       lorA
         (Write ((phi v0 : [%v0: int]) : [%v: unit]))
         (Read ((phi v : [%v0: unit]) : [%v: int]));
       starA (compA (Write ((true : [%v0: int]) : [%v: unit]))));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let[@effrty] boolGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let rec prog (dummy0 : unit) : unit =
  let (cond : bool) = perform (BoolGen ()) in
  if cond then
    let (dummy1 : unit) = perform (Write 0) in
    let (dummy2 : int) = perform (Read ()) in
    ()
  else
    let (dummy3 : unit) = prog () in
    let (n : int) = perform (Read ()) in
    let (m : int) = n + 2 in
    let (dummy4 : unit) = perform (Write m) in
    let (dummy5 : int) = perform (Read ()) in
    ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre = starA anyA;
    post =
      ((starA anyA;
        Read ((v mod 2 == 0 : [%v0: unit]) : [%v: int]);
        Ret (true : [%v0: unit])) : unit);
  }
