let minimum (default : Elem.t) : Elem.t =
  if isWritten () then
    let (min : Elem.t) = read () in
    min
  else default

let[@assertRty] minimum ((m : Elem.t) [@ghost]) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: Elem.t]); post = rI m }
