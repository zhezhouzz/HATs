type effect =
  | Initialise of (unit -> unit)
  | StartTask of (unit -> unit)
  | FinishTask of (unit -> unit)
  | WriteHeaders of (int -> unit)
  | WriteContent of (int -> unit)
  | NatGen of (unit -> int)

let[@effrty] initialise ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] startTask ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (starA anyA;
       Initialise (true : [%v0: unit]);
       starA (NatGen (true : [%v0: unit])));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] finishTask ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (starA anyA;
       StartTask (true : [%v0: unit]);
       starA (NatGen (true : [%v0: unit])));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] writeHeaders ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       FinishTask (true : [%v0: unit]);
       starA (NatGen (true : [%v0: unit])));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] writeContent ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       WriteHeaders (true : [%v0: int]);
       starA (NatGen (true : [%v0: unit])));
    post = (Ret (true : [%v0: unit]) : unit);
  }

(* let[@effrty] boolGen ?l:(a = (true : [%v: unit])) = *)
(*   { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) } *)

let[@effrty] natGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (0 <= v0 : [%v0: int]) : int) }

let prog (dummy0 : unit) : unit =
  let (dummy1 : unit) = perform (Initialise ()) in
  let (dummy2 : unit) = perform (StartTask ()) in
  let (dummy3 : unit) = perform (FinishTask ()) in
  let (n : int) = perform (NatGen ()) in
  let (dummy4 : unit) = perform (WriteHeaders n) in
  let (m : int) = perform (NatGen ()) in
  let (dummy5 : unit) = perform (WriteContent m) in
  ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre = starA anyA;
    post =
      ((starA anyA;
        WriteHeaders (0 <= v0 : [%v0: int]);
        starA (NatGen (true : [%v0: unit]));
        WriteContent (0 <= v0 : [%v0: int]);
        Ret (true : [%v0: unit])) : unit);
  }
