let rec empty (u : unit) : Cell.t =
  let (c : Cell.t) = newCell () in
  if isCell c then
    let (c' : Cell.t) = empty () in
    c'
  else c

let[@assertRty] empty ?l:(len = (true : [%v: unit])) =
  { pre = rI; res = (true : [%v: Cell.t]); post = rI }
