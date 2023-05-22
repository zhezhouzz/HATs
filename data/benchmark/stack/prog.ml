type effect = Push of (int -> unit) | Pop of (unit -> int)

let[@effrty] push ?l:(a = (true : [%v: int])) =
  { pre = epsilon; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] pop ?l:(a = (true : [%v: unit])) =
  let phi = (true : [%v: int -> bool]) in
  { pre = Push (phi v0 : [%v0: int]); post = (Ret (phi v0 : [%v0: int]) : int) }

let rec prog (u : unit) : unit =
  let (cond1 : bool) = bool_gen () in
  if cond1 then ()
  else
    let (dummy2 : unit) = prog () in
    let (m1 : int) = perform (Pop ()) in
    let (m2 : int) = m1 + 1 in
    let (dummy1 : unit) = perform (Push m2) in
    ()

let[@assert] prog ?l:(u = (true : [%v: unit]) [@over]) =
  {
    pre = Push (v0 == 0 : [%v0: int]);
    post =
      ((star
          (Pop (true : [%v0: unit]);
           Push (v0 >= 0 : [%v0: int]));
        Ret (true : [%v0: unit])) : unit);
  }
