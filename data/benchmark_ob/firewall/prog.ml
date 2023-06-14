type effect =
  | IsDevice of (int -> bool)
  | AddDevice of (int -> unit)
  | DeleteDevice of (int -> unit)
  | MakeCentral of (int -> unit)
  | FindCentral of (unit -> int)
  | BoolGen of (unit -> bool)

let[@effrty] boolGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

(* let[@effrty] natRange ?l:(a = (true : [%v: int])) ?l:(b = (a <= v : [%v: int])) *)
(*     = *)
(*   { pre = starA anyA; post = (Ret (a <= v0 && v0 <= b : [%v0: int]) : int) } *)

let[@effrty] isDevice ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       AddDevice ((v0 == a : [%v0: int]) : [%v: unit]);
       starA (anyA - DeleteDevice ((v0 == a : [%v0: int]) : [%v: unit])));
    post = (Ret (v0 : [%v0: bool]) : bool);
  }

let[@effrty] isDevice ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       DeleteDevice ((v0 == a : [%v0: int]) : [%v: unit]);
       starA (anyA - AddDevice ((v0 == a : [%v0: int]) : [%v: unit])))
      || starA (anyA - AddDevice ((v0 == a : [%v0: int]) : [%v: unit]));
    post = (Ret (not v0 : [%v0: bool]) : bool);
  }

let[@effrty] addDevice ?l:(a = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] deleteDevice ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       MakeCentral ((not (v0 == a) : [%v0: int]) : [%v: unit])
       || FindCentral ((not (v == a) : [%v0: unit]) : [%v: int]);
       starA (anyA - MakeCentral ((true : [%v0: int]) : [%v: unit])));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] makeCentral ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       AddDevice ((v0 == a : [%v0: int]) : [%v: unit]);
       starA (anyA - DeleteDevice ((v0 == a : [%v0: int]) : [%v: unit])));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] findCentral ?l:(a = (true : [%v: unit])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (starA anyA;
       MakeCentral ((phi v0 : [%v0: int]) : [%v: unit])
       || FindCentral ((phi v : [%v0: unit]) : [%v: int]);
       starA (anyA - MakeCentral ((true : [%v0: int]) : [%v: unit])));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let rec prog (lo : int) (hi : int) : unit =
  let (dummy10 : unit) =
    if lo > hi then ()
    else
      let (dummy3 : unit) = prog (lo + 1) hi in
      let (central : int) = perform (FindCentral ()) in
      let (dummy1 : unit) =
        if lo <= central && central <= hi then
          let (new_central : int) = hi + 1 in
          let (dummy2 : unit) = perform (AddDevice new_central) in
          let (dummy8 : unit) = perform (MakeCentral new_central) in
          ()
        else ()
      in
      if perform (BoolGen ()) then
        let (dummy4 : unit) = perform (AddDevice lo) in
        let (dummy6 : bool) = perform (IsDevice lo) in
        ()
      else ()
  in
  let (dummy9 : int) = perform (FindCentral ()) in
  ()

let[@assert] prog ?l:(lo = (true : [%v: int]) [@over])
    ?l:(hi = (true : [%v: int]) [@over]) =
  {
    pre =
      (starA anyA;
       MakeCentral ((true : [%v0: int]) : [%v: unit]);
       starA (anyA - MakeCentral ((true : [%v0: int]) : [%v: unit])));
    post =
      ((starA (anyA - DeleteDevice ((true : [%v0: int]) : [%v: unit]));
        (* FindCentral ((not (lo <= v && v <= hi) : [%v0: unit]) : [%v: int]); *)
        starA
          (IsDevice ((lo <= v0 && v0 <= hi + 1 && v : [%v0: int]) : [%v: bool]));
        FindCentral ((not (lo <= v && v <= hi) : [%v0: unit]) : [%v: int]);
        Ret (true : [%v0: unit])) : unit);
  }
