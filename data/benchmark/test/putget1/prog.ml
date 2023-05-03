let[@librty] ( <= ) =
  let[@pi] a = (true : [%v: int]) [@over] in
  let[@pi] b = (true : [%v: int]) [@over] in
  (iff v (a <= b) : [%v: bool]) [@under]

let[@librty] ( - ) =
  let[@pi] a = (true : [%v: int]) [@over] in
  let[@pi] b = (true : [%v: int]) [@over] in
  (v == a - b : [%v: int]) [@under]

let[@librty] mk_put =
  let[@pi] [@eff] a = (true : [%v: int * int]) [@over] in
  let[@pi] [@eff] b = (true : [%v: unit]) [@over] in
  (true : [%v: unit]) [@under]

let rec prog (n : int) : unit =
  if n <= 0 then ()
  else
    let (_ : unit) = perform (mk_put (n, n) ()) in
    prog (n - 1)

let[@rty] prog =
  let[@pi] n = (v >= 0 : [%v: int]) [@over] in
  ( len h == n && fun (u : [%forall: int]) ->
    implies (0 <= u && u < n) (select h u == mk_put (u, u) ()) ).h <-
    (true : [%v: unit]) [@under]
