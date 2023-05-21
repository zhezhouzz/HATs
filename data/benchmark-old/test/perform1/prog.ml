let[@librty] plus =
  let[@pi] [@eff] a = (true : [%v: int]) [@over] in
  let[@pi] [@eff] b = (true : [%v: int]) [@over] in
  (v == a + b : [%v: int]) [@under]

let rec prog (n : int) : int =
  let (n1 : int) = perform (plus n 1) in
  3

let[@rty] prog =
  let[@pi] n = (true : [%v: int]) [@over] in
  {
    h;
    pre = (true : [%v: tr]);
    rty = (v == 3 : [%v: int]) [@under];
    post = (true : [%v: tr]);
  }
