type effect = Put of (int -> int -> unit) | Get of (int -> int)

let prog (n : int) : int =
  if n <= 0 then 1
  else
    let (m : int) = int_gen () in
    if n == m then Err
    else
      let (dummy1 : unit) = perform (Put (n, m)) in
      let (dummy2 : int) = perform (Get n) in
      2

let[@assert] prog =
  let n = (v >= 0 : [%v: int]) [@over] in
  (lorA
     (Ret (v1 == 1 : [%v1: int]))
     (Put ((v1 == n && v2 != n : [%v1: int]) : [%v2: int]);
      Get (v1 == n : [%v1: int]);
      Ret (v1 == 2 : [%v1: int]))
    : int)
    [@regex]
