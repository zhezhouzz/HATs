let bar (x : int) = x + nat_gen ()

let[@assert] bar =
  let x = (v > 0 : [%v: int]) [@over] in
  (v == 1 || v == x : [%v: int])

let[@assert] bar =
  let x = (v > 0 : [%v: int]) [@over] in
  (v > 0 || v == x : [%v: int])

let[@assert] bar =
  let x = (v > 0 : [%v: int]) [@over] in
  (v == x + 1 : [%v: int])

let[@assert] bar =
  let x = (true : [%v: int]) [@over] in
  (v == x - 1 : [%v: int])

let[@assert] bar =
  let x = (v > 0 : [%v: int]) [@over] in
  (v == x - 1 : [%v: int])
