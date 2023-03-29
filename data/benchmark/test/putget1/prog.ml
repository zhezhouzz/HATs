let[@librty] ( <= ) =
  let[@pi] a = ((true : [%v: int]) : [%h: tr]) [@over] in
  let[@pi] b = ((true : [%v: int]) : [%h: tr]) [@over] in
  ((iff v (a <= b) && len h == 0 : [%v: bool]) : [%h: tr]) [@under]

let[@librty] ( - ) =
  let[@pi] a = ((true : [%v: int]) : [%h: tr]) [@over] in
  let[@pi] b = ((true : [%v: int]) : [%h: tr]) [@over] in
  ((v == a - b && len h == 0 : [%v: int]) : [%h: tr]) [@under]

let[@librty] mk_put =
  let[@pi] [@eff] a = ((true : [%v: int * int]) : [%h: tr]) [@over] in
  let[@pi] [@eff] b = ((true : [%v: unit]) : [%h: tr]) [@over] in
  ((len h == 0 : [%v: unit]) : [%h: tr]) [@under]

let rec prog (n : int) : unit =
  if n <= 0 then ()
  else
    let (_ : unit) = perform (mk_put (n, n) ()) in
    prog (n - 1)

let[@rty] prog =
  let[@pi] n = ((v >= 0 : [%v: int]) : [%h: tr]) [@over] in
  ((len h == n && fun (u : [%forall: int]) ->
    implies (0 <= u && u < n) (select h u == mk_put (u, u) ())
     : [%v: unit])
    : [%h: tr])
    [@under]
