type effect =
  | Subcribe of (int -> int -> unit)
  | Unsubcribe of (int -> int -> unit)
  | Confirm of (int -> int -> int -> unit)
  | Select of (int -> int -> bool)
  | BoolGen of (unit -> bool)
  | IntGen of (unit -> int)

let[@effrty] subcribe ?l:(user = (true : [%v: int]))
    ?l:(news = (true : [%v: int])) =
  {
    pre =
      lorA
        (starA anyA;
         Unsubcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]);
         starA
           (compA
              (Subcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]))))
        (starA
           (compA
              (Subcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] unsubcribe ?l:(user = (true : [%v: int]))
    ?l:(news = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Subcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]);
       starA
         (compA
            (Unsubcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] confirm ?l:(user = (true : [%v: int]))
    ?l:(news = (true : [%v: int])) ?l:(code = (0 <= v && v <= 2 : [%v: int])) =
  {
    pre =
      (starA anyA;
       Subcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]);
       starA
         (compA
            (Unsubcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] select ?l:(user = (true : [%v: int]))
    ?l:(news = (true : [%v: int])) =
  {
    pre =
      lorA
        (starA anyA;
         Unsubcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]);
         starA
           (compA
              (Subcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]))))
        (starA
           (compA
              (Subcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]))));
    post = (Ret (not v0 : [%v0: bool]) : bool);
  }

let[@effrty] select ?l:(user = (true : [%v: int]))
    ?l:(news = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Subcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]);
       starA
         (compA
            (Unsubcribe ((v0 == user && v1 == news : [%v0: int]) : [%v1: int]))));
    post = (Ret (v0 : [%v0: bool]) : bool);
  }

let[@effrty] boolGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: bool]) : bool) }

let[@effrty] intGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (true : [%v0: int]) : int) }

let rec prog (dummy0 : unit) : unit =
  let (cond : bool) = perform (BoolGen ()) in
  if cond then ()
  else
    let (user : int) = perform (IntGen ()) in
    let (news : int) = perform (IntGen ()) in
    let (if_subcribed : bool) = perform (Select (user, news)) in
    if if_subcribed then
      let (dummy1 : unit) = prog () in
      ()
    else
      let (dummy2 : unit) = perform (Subcribe (user, news)) in
      let (dummy3 : unit) = perform (Confirm (user, news, 1)) in
      let (dummy4 : unit) = prog () in
      ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre = starA anyA;
    post =
      ((starA anyA;
        Ret (true : [%v0: unit])) : unit);
  }
