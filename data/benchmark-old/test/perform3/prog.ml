let[@librty] ( <= ) =
  let[@pi] a = (true : [%v: int]) [@over] in
  let[@pi] b = (true : [%v: int]) [@over] in
  (iff v (a <= b) : [%v: bool]) [@under]

let[@librty] ( - ) =
  let[@pi] a = (true : [%v: int]) [@over] in
  let[@pi] b = (true : [%v: int]) [@over] in
  (v == a - b : [%v: int]) [@under]

let[@librty] plus =
  let[@pi] [@eff] a = (true : [%v: int]) [@over] in
  let[@pi] [@eff] b = (true : [%v: int]) [@over] in
  (v == a + b : [%v: int]) [@under]

let rec prog (n : int) : int =
  let (n1 : int) = perform (plus n 1) in
  let (n2 : int) = perform (plus n1 1) in
  let (n3 : int) = perform (plus n2 1) in
  if n <= 0 then
    let (n4 : int) = perform (plus n3 2) in
    let (n5 : int) = perform (plus n4 2) in
    n5
  else
    let (n6 : int) = perform (plus n3 1) in
    let (n7 : int) = perform (plus n6 1) in
    n7

let[@rty] prog =
  let[@pi] n = (true : [%v: int]) [@over] in
  {
    h;
    pre = (true : [%v: tr]);
    rty = ((n <= 0 && v == n + 7) || (n > 0 && v == n + 5) : [%v: int]) [@under];
    post = (true : [%v: tr]);
  }
