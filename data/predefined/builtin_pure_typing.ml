let[@librty] ( && ) ?l:(a = (true : [%v: bool]) [@over])
    ?l:(b = (true : [%v: bool]) [@over]) : [%v: bool] =
  iff v (a && b)

let[@librty] ( == ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@librty] eqn ?l:(a = (true : [%v: nat]) [@over])
    ?l:(b = (true : [%v: nat]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@librty] ( != ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a != b)

let[@librty] ( < ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a < b)

let[@librty] ( > ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a > b)

let[@librty] ( <= ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a <= b)

let[@librty] ( >= ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a >= b)

let[@librty] ( + ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a + b

let[@librty] ( - ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a - b

let[@librty] ( mod ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a mod b

let[@librty] ( * ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a * b

let[@librty] ( / ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (not (v == 0) : [%v: int]) [@over]) : [%v: int] =
  v == a / b

let[@librty] increment ?l:(n = (true : [%v: int]) [@over]) : [%v: int] =
  v == n + 1

let[@librty] decrement ?l:(n = (true : [%v: int]) [@over]) : [%v: int] =
  v == n - 1

(* randomness operators are now effectful *)

(* let[@librty] int_range ?l:(a = (true : [%v: int]) [@over]) *)
(*     ?l:(b = (1 + a < v : [%v: int]) [@over]) : [%v: int] = *)
(*   a < v && v < b *)

(* let[@librty] bool_gen ?l:(_ = (true : [%v: unit]) [@over]) : [%v: bool] = true *)
(* let[@librty] int_gen ?l:(_ = (true : [%v: unit]) [@over]) : [%v: int] = true *)
(* let[@librty] nat_gen ?l:(_ = (true : [%v: unit]) [@over]) : [%v: int] = v >= 0 *)

(* let[@librty] int_range_inc ?l:(a = (true : [%v: int]) [@over]) *)
(*     ?l:(b = (a <= v : [%v: int]) [@over]) : [%v: int] = *)
(*   a <= v && v <= b *)

(* let[@librty] int_range_inex ?l:(a = (true : [%v: int]) [@over]) *)
(*     ?l:(b = (a <= v : [%v: int]) [@over]) : [%v: int] = *)
(*   a <= v && v < b *)
