let foo (x : int) : int = x + 1

let[@assert] foo =
  let x = (v > 0 : [%v: int]) in
  (v == x + 1 : [%v: int])

let[@assert] foo =
  let x = (v > 0 : [%v: int]) in
  (v > 1 : [%v: int])

let[@assert] foo =
  let x = (v > 0 : [%v: int]) in
  (v == 2 : [%v: int])

let[@assert] foo =
  let x = (true : [%v: int]) in
  (v == 2 : [%v: int])

let[@assert] foo =
  let x = (true : [%v: int]) in
  (false : [%v: int])

let[@assert] foo =
  let x = (true : [%v: int]) in
  (true : [%v: int])

let[@assert] foo =
  let x = (false : [%v: int]) in
  (false : [%v: int])

let[@assert] foo =
  let x = (v > 0 : [%v: int]) in
  (v == 2 || v == 3 : [%v: int])
