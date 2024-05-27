let rec cons (x : Elem.t) (s : Cell.t) : Cell.t =
  if hasPrev s then s
  else
    let (c : Cell.t) = newCell () in
    if cell_eq c s then
      let (c' : Cell.t) = cons x s in
      c'
    else (
      putCellContent c x;
      setNext c s;
      c)

let[@assertRty] cons ?l:(x = (true : [%v: Elem.t]))
    ?l:(s = (true : [%v: Cell.t])) =
  { pre = rI; res = (true : [%v: Cell.t]); post = rI }
