type effect = Put of (int -> int -> unit) | Get of (int -> int)

let[@effrty] put ?l:(a = (true : [%v: int])) ?l:(b = (true : [%v: int])) =
  { pre = epsilon; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] get ?l:(a = (true : [%v: int])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (Put ((v0 == a && phi v1 : [%v0: int]) : [%v1: int]);
       star
         (lorA
            (Get (true : [%v0: int]))
            (Put ((not (v0 == a) : [%v0: int]) : [%v1: int]))));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let rec prog (n : int) : unit =
  if n <= 0 then ()
  else
    let (m : int) = nat_gen () in
    let (dummy1 : unit) = perform (Put (n, m)) in
    let (n1 : int) = n - 1 in
    let (dummy2 : unit) = prog n1 in
    ()

let[@assert] prog ?l:(n = (v >= 0 : [%v: int]) [@over]) =
  {
    pre = epsilon;
    post =
      ((star (Put ((0 < v0 && v0 <= n && 0 <= v1 : [%v0: int]) : [%v1: int]));
        Ret (true : [%v0: unit])) : unit);
  }
