type effect =
  | Insert of (int -> unit)
  | Mem of (int -> bool)
  | BoolGen of (unit -> bool)
  | EvenGen of (unit -> int)

let[@effrty] insert ?l:(a = (true : [%v: int])) =
  {
    pre = starA (compA (Insert (v0 == a : [%v0: int])));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] mem ?l:(a = (true : [%v: int])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (starA anyA;
       Insert (phi v0 : [%v0: int]);
       starA anyA);
    post = (Ret (v0 : [%v0: bool]) : bool);
  }

let[@effrty] mem ?l:(a = (true : [%v: int])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre = starA (compA (Insert (phi v0 : [%v0: int])));
    post = (Ret (not v0 : [%v0: bool]) : bool);
  }

let[@effrty] boolGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let[@effrty] evenGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (v0 mod 2 == 0 : [%v0: int]) : int) }

let rec prog (dummy0 : unit) : unit =
  let (cond : bool) = perform (BoolGen ()) in
  if cond then ()
  else
    let (n : int) = perform (EvenGen ()) in
    let (ifin : bool) = perform (Mem n) in
    if ifin then
      let (dummy1 : unit) = prog () in
      ()
    else
      let (dummy2 : unit) = perform (Insert n) in
      let (dummy3 : unit) = prog () in
      ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre = starA (compA (Insert (v0 mod 2 == 1 : [%v0: int])));
    post =
      ((starA (compA (Insert (v0 mod 2 == 1 : [%v0: int])));
        Ret (true : [%v0: unit])) : unit);
  }
