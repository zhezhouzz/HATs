type effect =
  | Put of (int -> int -> unit)
  | Get of (int -> int)
  | EvenGen of (unit -> int)

let[@effrty] put ?l:(a = (true : [%v: int])) ?l:(b = (true : [%v: int])) =
  { pre = starA anyA; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] get ?l:(a = (true : [%v: int])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (starA anyA;
       Put ((v0 == a && phi v1 : [%v0: int]) : [%v1: int]);
       starA (compA (Put ((v0 == a : [%v0: int]) : [%v1: int]))));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let[@effrty] evenGen ?l:(a = (true : [%v: unit])) =
  { pre = starA anyA; post = (Ret (v0 mod 2 == 0 : [%v0: int]) : int) }

let rec prog (lo : int) (hi : int) : unit =
  let (dummy1 : unit) = perform (Put (lo, 0)) in
  if hi <= lo then ()
  else
    let (hi2 : int) = hi - 1 in
    let (dummy2 : unit) = prog lo hi2 in
    let (n : int) = perform (EvenGen ()) in
    let (last : int) = perform (Get lo) in
    let (m2 : int) = last + n in
    let (dummy3 : unit) = perform (Put (hi, m2)) in
    ()

let[@assert] prog ?l:(lo = (true : [%v: int]) [@over])
    ?l:(hi = (lo <= v : [%v: int]) [@over]) =
  {
    pre = starA anyA;
    post =
      ((Put ((v0 == lo && v1 mod 2 == 0 : [%v0: int]) : [%v1: int]);
        starA
          (compA
             (Put
                (((v0 <= hi && lo <= v0) && not (v1 mod 2 == 0) : [%v0: int])
                  : [%v1: int])));
        Ret (true : [%v0: unit])) : unit);
  }
