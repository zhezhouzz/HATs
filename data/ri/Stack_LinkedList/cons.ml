let rec cons (x : Elem.t) (s : Cell.t) : Cell.t =
  if hasPrev s then s
  else
    let (c : Cell.t) = newCell () in
    putCellContent c x;
    setNext c s;
    c

let[@assertRty] cons ?l:(x = (true : [%v: Elem.t]))
    ?l:(s = (true : [%v: Cell.t])) =
  { pre = rI && is_cell s; res = (true : [%v: Cell.t]); post = rI }
