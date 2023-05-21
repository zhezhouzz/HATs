let[@librty] tr_len =
  let[@pi] [@eff] a = (true : [%v: tr]) [@over] in
  (true : [%v: int]) [@under]

let[@librty] plus =
  let[@pi] [@eff] a = (true : [%v: int]) [@over] in
  let[@pi] [@eff] b = (true : [%v: int]) [@over] in
  (v == a + b : [%v: int]) [@under]

let[@librty] dummy =
  let[@pi] [@eff] a = (true : [%v: unit]) [@over] in
  {
    h;
    pre = (true : [%v: tr]);
    rty = (v == tr_len h : [%v: int]) [@under];
    post = (true : [%v: tr]);
  }

let rec prog (n : int) : int =
  let (n1 : int) = perform (plus n 1) in
  let (n2 : int) = perform (dummy ()) in
  n2

let[@rty] prog =
  let[@pi] n = (true : [%v: int]) [@over] in
  {
    h;
    pre = (true : [%v: tr]);
    rty = (v == n + 2 : [%v: int]) [@under];
    post = (true : [%v: tr]);
  }
