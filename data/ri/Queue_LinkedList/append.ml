let rec append (hd : Cell.t) (x : Elem.t) : unit =
  if isCell hd then
    if hasCellContent hd then
      let (c : Cell.t) = newCell () in
      if cell_eq hd c then (
        append hd x;
        ())
      else (
        setNext hd c;
        putCellContent c x;
        ())
    else (
      putCellContent hd x;
      ())
  else ()

let[@assertRty] append ?l:(hd = (true : [%v: Cell.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
