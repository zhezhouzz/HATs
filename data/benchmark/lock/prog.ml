type effect = Lock of (unit -> unit) | Unlock of (unit -> unit)

let[@effrty] lock ?l:(a = (true : [%v: unit])) =
  {
    pre =
      star
        (Lock (true : [%v0: unit]);
         Unlock (true : [%v0: unit]));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let[@effrty] unlock ?l:(a = (true : [%v: unit])) =
  {
    pre =
      (star
         (Lock (true : [%v0: unit]);
          Unlock (true : [%v0: unit]));
       Lock (true : [%v0: unit]));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let rec prog (n : int) : unit =
  if n <= 0 then
    let (dummy1 : unit) = perform (Lock ()) in
    ()
  else
    let (dummy1 : unit) = perform (Lock ()) in
    let (dummy2 : unit) = perform (Unlock ()) in
    let (n' : int) = n - 1 in
    let (dummy3 : unit) = prog n' in
    ()

let[@assert] prog ?l:(n = (v >= 0 : [%v: int]) [@over]) =
  {
    pre =
      star
        (Lock (true : [%v0: unit]);
         Unlock (true : [%v0: unit]));
    post =
      ((star
          (Lock (true : [%v0: unit]);
           Unlock (true : [%v0: unit]));
        Lock (true : [%v0: unit]);
        Ret (true : [%v0: unit])) : unit);
  }
