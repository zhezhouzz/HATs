let[@librty] plus =
  let[@pi] [@eff] a = (true : [%v: int]) [@over] in
  let[@pi] [@eff] b = (true : [%v: int]) [@over] in
  (v == a + b : [%v: int]) [@under]

let rec prog (n : int) : int =
  let (n1 : int) = perform (plus n 1) in
  let (n2 : int) = perform (plus n1 1) in
  n2

let[@rty] prog =
  let[@pi] n = (true : [%v: int]) [@over] in
  {
    h;
    pre = (true : [%v: tr]);
    rty = (v == n + 2 : [%v: int]) [@under];
    post = (true : [%v: tr]);
  }
