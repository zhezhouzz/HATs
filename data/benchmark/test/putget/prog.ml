type effect = Put of (int -> int -> unit) | Get of (int -> int)

let[@equation] ret_of_put =
  eqr
    (let a = Put (b, c) in
     Ret a)
    (Ret ())

let[@equation] ret_of_get =
  eqr
    (let a = Get b in
     Ret a)
    (Ret 0)

let prog (n : int) : int =
  if n <= 0 then 1
  else
    let (m : int) = int_gen () in
    if n == m then Err
    else
      let (dummy1 : unit) = perform (Put (n, m)) in
      2

let[@assert] prog ?l:(n = (v >= 0 : [%v: int]) [@over]) : (int[@regex]) =
  Put ((v0 == n && n > 0 && v1 != n : [%v0: int]) : [%v1: int]);
  Ret (v0 == 2 : [%v0: int])

(* let[@assert] prog ?l:(n = (v >= 0 : [%v: int]) [@over]) : (int[@regex]) = *)
(*   Put ((v1 == n && v2 != n : [%v1: int]) : [%v2: int]); *)
(*   Ret (v1 == 2 : [%v1: int]) *)

(* let[@assert] prog ?l:(n = (v >= 0 : [%v: int]) [@over]) : (int[@regex]) = *)
(*   lorA *)
(*     (Ret (v1 == 1 : [%v1: int])) *)
(*     (Put ((v1 == n && v2 != n : [%v1: int]) : [%v2: int]); *)
(*      Ret (v1 == 2 : [%v1: int])) *)
