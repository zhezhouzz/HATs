let rec cons (x : Elem.t) (s : Cell.t) : Cell.t =
  if existsValC s then s
  else
    let (c : Cell.t) = newCell () in
    if existsValC c then
      let (c' : Cell.t) = cons x s in
      c'
    else if existsC c then
      let (c' : Cell.t) = cons x s in
      c'
    else (
      putE c x;
      putC c s;
      c)

let[@assertRty] cons ((a : Cell.t) [@ghost]) ?l:(x = (true : [%v: Elem.t]))
    ?l:(s = (true : [%v: Cell.t])) =
  { pre = rI a; res = (true : [%v: Cell.t]); post = rI a }
