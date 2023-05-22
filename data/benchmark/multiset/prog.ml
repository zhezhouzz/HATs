type effect = Insert of (int -> unit) | Delete of (int -> unit)

let[@effrty] insert ?l:(a = (true : [%v: int])) =
  { pre = epsilon; post = (Ret (true : [%v0: unit]) : unit) }

let[@effrty] delete ?l:(a = (true : [%v: int])) =
  {
    pre =
      (Insert (v0 == a : [%v0: int]);
       star (complement (Delete (v0 == a : [%v0: int]))));
    post = (Ret (true : [%v0: unit]) : unit);
  }

let rec prog (n : int) : unit =
  if n <= 0 then ()
  else
    let (dummy1 : unit) = perform (Insert n) in
    let (dummy2 : unit) = prog (n - 1) in
    ()

let[@assert] prog ?l:(n = (0 <= v : [%v: int]) [@over]) =
  {
    pre = epsilon;
    post =
      ((star (Insert (0 < v0 && v0 <= n : [%v0: int]));
        Ret (true : [%v0: unit])) : unit);
  }
