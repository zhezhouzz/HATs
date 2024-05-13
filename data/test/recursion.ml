val write : int -> unit

let iter (x : int) : unit =
  let rec loop : int -> unit =
   fun (i : int) ->
    if i == x then (
      write (-1);
      ())
    else (
      write i;
      loop (i - 1))
  in
  loop 0
