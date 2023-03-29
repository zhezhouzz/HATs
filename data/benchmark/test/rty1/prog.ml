let[@rty] rty0 = ((v == (x > y) : [%v: int]) : [%h: tr]) [@under]

let[@rty] rty1 =
  let[@pi] x = ((v > 0 : [%v: int]) : [%h: tr]) [@over] in
  let[@pi] y = ((v > 0 : [%v: int]) : [%h: tr]) [@over] in
  ((iff v (x > y) : [%v: int]) : [%h: tr]) [@under]

let[@librty] rty2 =
  let[@sigma] x = ((v > 0 : [%v: int]) : [%h: tr]) [@under] in
  let[@sigma] y = ((v > 0 : [%v: int]) : [%h: tr]) [@under] in
  ((v == x > y : [%v: int]) : [%h: tr]) [@under]

let[@rty] prog =
  let[@pi] n = ((v >= 0 : [%v: int]) : [%h: tr]) [@over] in
  ((fun (u : [%forall: int]) ->
      implies (0 <= u && u < n) (h u == mk_put (u, u) ())
     : [%v: unit])
    : [%h: tr])
    [@under]
