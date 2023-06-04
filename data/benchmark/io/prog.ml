type effect = Write of (int -> unit) | Read of (unit -> int)

let[@effrty] write ?l:(a = (true : [%v: int])) =
  { pre = star any; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] read ?l:(a = (true : [%v: unit])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      (star any;
       Write (phi v0 : [%v0: int]);
       star (Read (true : [%v0: unit])));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let rec prog (dummy0 : unit) : unit =
  let (cond : bool) = bool_gen () in
  if cond then
    let (dummy1 : unit) = perform (Write 0) in
    ()
  else
    let (dummy2 : unit) = prog () in
    let (n : int) = perform (Read ()) in
    let (m : int) = n + 2 in
    let (dummy3 : unit) = perform (Write m) in
    ()

let[@assert] prog ?l:(n = (true : [%v: unit]) [@over]) =
  {
    pre = star any;
    post =
      ((star any;
        Write (v0 mod 2 == 0 : [%v0: int]);
        Ret (true : [%v0: unit])) : unit);
  }
