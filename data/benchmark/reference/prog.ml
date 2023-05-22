type effect = Mkref of (int -> unit) | Deref of (unit -> int)

let[@effrty] mkref ?l:(a = (true : [%v: int])) =
  { pre = epsilon; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] deref ?l:(a = (true : [%v: unit])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (Mkref (phi v0 : [%v0: int]);
       star (Deref (true : [%v0: unit])));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let rec prog (n : int) : unit =
  let (dummy1 : unit) = perform (Mkref n) in
  let (cond : bool) = bool_gen () in
  if cond then ()
  else
    let (dummy2 : int) = perform (Deref ()) in
    let (dummy3 : unit) = prog n in
    ()

let[@assert] prog ?l:(n = (v >= 0 : [%v: int]) [@over]) =
  {
    pre = epsilon;
    post =
      ((star
          (Mkref (v0 == n : [%v0: int]);
           Deref (true : [%v0: unit]));
        Mkref (v0 == n : [%v0: int]);
        Ret (true : [%v0: unit])) : unit);
  }
