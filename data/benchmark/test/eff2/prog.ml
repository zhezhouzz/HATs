type effect = Put of (int -> int -> unit) | Get of (int -> int)

let rec prog (n : int) : unit =
  if n <= 0 then ()
  else
    let (dummy1 : unit) = Put (n, int_gen ()) in
    let (dummy2 : int) = Get n in
    prog (n - 1)
