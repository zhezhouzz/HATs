let rec empty (u : unit) : Cell.t =
  let (c : Cell.t) = newCell () in
  if existsValC c then
    let (c' : Cell.t) = empty () in
    c'
  else if existsC c then
    let (c' : Cell.t) = empty () in
    c'
  else c

let[@assertRty] empty ((a : Cell.t) [@ghost]) ?l:(x = (true : [%v: unit])) =
  { pre = rI a; res = (true : [%v: Cell.t]); post = rI a }
