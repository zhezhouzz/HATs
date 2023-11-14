let rec head (default : Elem.t) (s : Cell.t) : Elem.t =
  if existsE s then
    let (x : Elem.t) = getE s in
    x
  else default

let[@assertRty] head ((a : Cell.t) [@ghost]) ?l:(x = (true : [%v: Elem.t]))
    ?l:(y = (true : [%v: Cell.t])) =
  { pre = rI a; res = (true : [%v: Elem.t]); post = rI a }
