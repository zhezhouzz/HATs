let add_edge_aux (st : Node.t) (en : Node.t) : unit =
  if existsE st en then
    let (c1 : Color.t) = getC st in
    let (c2 : Color.t) = getC en in
    if color_eq c1 c2 then ()
    else (
      putE st en;
      ())
  else ()

let[@assertRty] add_edge_aux ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ((c : Color.t) [@ghost]) ?l:(st = (true : [%v: Node.t]))
    ?l:(en = (true : [%v: Node.t])) =
  {
    pre = rI s1 s2 c && existsCP st && existsCP en;
    res = (true : [%v: unit]);
    post = rI s1 s2 c;
  }
