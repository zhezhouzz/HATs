type effect =
  | OpenDB of (unit -> unit)
  | CloseDB of (unit -> unit)
  | PrepareStatement of (int -> unit)
  | BindInt of (int -> unit)
  | FinishBind of (unit -> unit)
  | ExecuteStatement of (unit -> unit)
  | BoolGen of (unit -> bool)
  | NatGen of (unit -> int)

let[@effrty] openDB ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] closeDB ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (starA anyA;
       OpenDB (true : [%v0: unit]);
       starA (compA (CloseDB (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] prepareStatement ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       OpenDB (true : [%v0: unit]);
       starA (compA (CloseDB (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] bindInt ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       PrepareStatement (true : [%v0: int]);
       starA (compA (FinishBind (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] finishBind ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (starA anyA;
       PrepareStatement (true : [%v0: int]);
       starA (compA (FinishBind (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] executeStatement ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (starA anyA;
       FinishBind (true : [%v0: unit]);
       starA (compA (CloseDB (true : [%v0: unit]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

(* let[@effrty] rowStep ?l:(a = (true : [%v: unit])) = *)
(*   { *)
(*     pre = *)
(*       (starA anyA; *)
(*        ExecuteStatement (true : [%v0: unit]); *)
(*        starA *)
(*          (lorA *)
(*             (EvenGen (true : [%v0: unit])) *)
(*             (lorA (BoolGen (true : [%v0: unit])) (RowStep (true : [%v0: unit]))))); *)
(*     post = (Ret (true : [%v0: unit]) : unit); *)
(*   } *)

let[@effrty] boolGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let[@effrty] natGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (0 <= v0 : [%v0: int]) : int) }

let rec prog (dummy0 : unit) : unit =
  let (dummy1 : unit) = perform (OpenDB ()) in
  let (stat : int) = perform (NatGen ()) in
  let (dummy2 : unit) = perform (PrepareStatement stat) in
  let (n : int) = perform (NatGen ()) in
  let (dummy3 : unit) = perform (BindInt n) in
  let (m : int) = perform (NatGen ()) in
  let (dummy4 : unit) = perform (BindInt m) in
  let (dummy5 : unit) = perform (FinishBind ()) in
  let (dummy6 : unit) = perform (ExecuteStatement ()) in
  ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre = starA anyA;
    post =
      ((starA (compA (BindInt (1 > v0 : [%v0: int])));
        ExecuteStatement (true : [%v0: unit]);
        Ret (true : [%v0: unit])) : unit);
  }
