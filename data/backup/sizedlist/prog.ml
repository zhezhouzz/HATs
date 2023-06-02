type effect = Cons of (int -> unit) | Decons of (unit -> int)

let[@effrty] cons ?l:(a = (true : [%v: int])) =
  { pre = epsilon; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] decons ?l:(a = (true : [%v: unit])) =
  let phi = (true : [%v: int -> bool]) in
  {
    pre =
      lorA
        (Cons (phi v0 : [%v0: int]))
        (Cons (phi v0 : [%v0: int]);
         star
           (Cons (true : [%v0: int]);
            Decons (true : [%v0: unit])));
    post = (Ret (phi v0 : [%v0: int]) : int);
  }

let rec prog (u : unit) : unit =
  let (cond1 : bool) = bool_gen () in
  if cond1 then ()
  else
    let (dummy2 : unit) = prog () in
    let (m1 : int) = perform (Decons ()) in
    let (m2 : int) = m1 + 1 in
    let (dummy1 : unit) = perform (Cons m2) in
    ()

let[@assert] prog ?l:(u = (true : [%v: unit]) [@over]) =
  {
    pre = Cons (v0 == 0 : [%v0: int]);
    post =
      ((star
          (Decons (true : [%v0: unit]);
           Cons (v0 >= 0 : [%v0: int]));
        Ret (true : [%v0: unit])) : unit);
  }
