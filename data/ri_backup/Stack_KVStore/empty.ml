let rec empty (u : unit) : Cell.t =
  let (c : Cell.t) = newCell () in
  if exists c then
    let (c' : Cell.t) = empty () in
    c'
  else c
