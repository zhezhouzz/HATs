let[@rty] rty0 = true.h <- (v == 3 : [%v: int]) [@under]

let[@rty] rty1 =
  let[@pi] x = (v > 0 : [%v: int]) [@over] in
  let[@pi] y = (v > 0 : [%v: int]) [@over] in
  (iff v (x > y) : [%v: bool]) [@under]

let[@librty] rty2 =
  let[@sigma] x = (v > 0 : [%v: int]) [@under] in
  let[@sigma] y = (v > 0 : [%v: int]) [@under] in
  (v == (x > y) : [%v: bool]) [@under]

let[@rty] prog =
  let[@pi] n = (v >= 0 : [%v: int]) [@over] in
  (fun (u : [%forall: int]) -> implies (0 <= u && u < n) (select h u == ())).h <-
    (true : [%v: unit]) [@under]
