type effect = Snoc of (int -> unit) | Tail of (unit -> int)

let[@effrty] snoc ?l:(a = (true : [%v: int])) =
  { pre = epsilon; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] tail ?l:(a = (true : [%v: unit])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      lorA
        (Snoc (phi v0 : [%v0: int]);
         Snoc (true : [%v0: int]))
        (Snoc (phi v0 : [%v0: int]);
         star
           (Snoc (true : [%v0: int]);
            Tail (true : [%v0: unit]));
         Snoc (true : [%v0: int]));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let rec prog (u : unit) : unit =
  let (cond1 : bool) = bool_gen () in
  if cond1 then ()
  else
    let (dummy2 : unit) = prog () in
    let (m1 : int) = perform (Tail ()) in
    let (m2 : int) = m1 + 1 in
    let (dummy1 : unit) = perform (Snoc m2) in
    ()

let[@assert] prog ?l:(u = (true : [%v: unit]) [@over]) =
  {
    pre =
      (Snoc (v0 == 0 : [%v0: int]);
       Snoc (v0 == 0 : [%v0: int]));
    post =
      ((star
          (Tail (true : [%v0: unit]);
           Snoc (v0 >= 0 : [%v0: int]));
        Ret (true : [%v0: unit])) : unit);
  }
