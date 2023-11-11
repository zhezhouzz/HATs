let rec snoc (hd : Cell.t) (x : Elem.t) : unit =
  if hasNext hd then (
    let (hd' : Cell.t) = getNext hd in
    snoc hd' x;
    ())
  else (
    append hd x;
    ())

let[@libRty] append ?l:(hd = (true : [%v: Cell.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }

let[@assertRty] snoc ?l:(hd = (true : [%v: Cell.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
