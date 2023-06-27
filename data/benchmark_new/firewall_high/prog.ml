type effect =
  | AddDevice of (int -> unit)
  | IsDevice of (int -> bool)
  | DeleteDevice of (int -> unit)
  | MakeCentral of (int -> unit)
(* | BoolGen of (unit -> bool) *)
(* | EvenGen of (unit -> int) *)

let[@effrty] addDevice ?l:(a = (true : [%v: int])) =
  {
    pre =
      lorA
        (starA anyA;
         DeleteDevice (v0 == a : [%v0: int]);
         starA (compA (AddDevice (v0 == a : [%v0: int]))))
        (starA (compA (AddDevice (v0 == a : [%v0: int]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] isDevice ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       AddDevice (v0 == a : [%v0: int]);
       starA (compA (DeleteDevice (v0 == a : [%v0: int]))));
    post = (Ret (v0 : [%v0: bool]) : bool);
  }

let[@effrty] isDevice ?l:(a = (true : [%v: int])) =
  {
    pre =
      lorA
        (starA anyA;
         DeleteDevice (v0 == a : [%v0: int]);
         starA (compA (AddDevice (v0 == a : [%v0: int]))))
        (starA (compA (AddDevice (v0 == a : [%v0: int]))));
    post = (Ret (not v0 : [%v0: bool]) : bool);
  }

let[@effrty] deleteDevice ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       AddDevice (v0 == a : [%v0: int]);
       starA (compA (DeleteDevice (v0 == a : [%v0: int])));
       MakeCentral (not (v0 == a) : [%v0: int]);
       starA (compA (DeleteDevice (v0 == a : [%v0: int]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] makeCentral ?l:(a = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       AddDevice (v0 == a : [%v0: int]);
       starA (compA (DeleteDevice (v0 == a : [%v0: int]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

(* let[@effrty] boolGen ?l:(a = (true : [%v: unit])) = *)
(*   { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) } *)

(* let[@effrty] intGen ?l:(a = (true : [%v: unit])) = *)
(*   { pre = starA anyA; post = (Ret (true : [%v0: int]) : int) } *)

let rec prog (n : int) : unit =
  if 0 == n then
    let (dummy0 : unit) = perform (AddDevice n) in
    let (dummy1 : unit) = perform (MakeCentral n) in
    ()
  else
    let (dummy2 : unit) = prog (n - 1) in
    let (dummy3 : unit) = perform (AddDevice n) in
    let (dummy4 : unit) = perform (MakeCentral n) in
    ()

let[@assert] prog ?l:(n = (0 <= v : [%v: int]) [@over]) =
  {
    pre = epsilonA;
    post =
      ((starA (compA (AddDevice (not (v0 <= n) : [%v0: int])));
        MakeCentral (v0 == n : [%v0: int]);
        Ret (true : [%v0: unit])) : unit);
  }
