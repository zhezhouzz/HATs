type effect = Put of (int -> int -> unit) | Get of (int -> int)

let rec prog (n : int) : unit =
  if n <= 0 then ()
  else
    let (dummy1 : unit) = Put (n, nat_gen ()) in
    let (dummy2 : int) = Get n in
    prog (n - 1)

(* let[@assert] prog = *)
(*   let n = (v >= 0 : [%v: int]) [@over] in *)
(*   mu x xA n *)
(*     (Ret *)
(*        (let n = (v >= 0 : [%v: int]) [@over] in *)
(*         (mu x xA n *)
(*            (Put ((v == x && w >= 0 : [%v: int]) : [%w: int]); *)
(*             Get (v == x : [%v: int]); *)
(*             Ret (true : [%v: unit])) *)
(*           : unit) *)
(*           [@over])) *)

let[@assert] prog =
  let n = (v >= 0 : [%v: int]) [@over] in
  (mu x xA n
     (lorA
        (Ret (true : [%v: unit]))
        (Put ((v == x && w >= 0 : [%v: int]) : [%w: int]);
         Get (v == x : [%v: int]);
         xA))
    : unit)
    [@regex]
