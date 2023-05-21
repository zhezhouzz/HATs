let neg_relu (x : int) : int = if 0 < x then int_gen () else 0

let[@assert] neg_relu =
  let x = (true : [%v: int]) [@over] in
  (v == 0 : [%v: int])

let[@assert] neg_relu =
  let x = (true : [%v: int]) [@over] in
  (v >= 0 : [%v: int])

let[@assert] neg_relu =
  let x = (v > 0 : [%v: int]) [@over] in
  (v > 0 : [%v: int])

let[@assert] neg_relu =
  let x = (v > 0 : [%v: int]) [@over] in
  (v >= 0 : [%v: int])
