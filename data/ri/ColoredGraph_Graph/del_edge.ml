let del_edge (st : Node.t) (en : Node.t) : unit =
  if isNode st then
    if isNode en then
      if isConnected st en then (
        disconnect st en;
        ())
      else ()
    else ()
  else ()

let[@assertRty] del_edge ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ((c : Color.t) [@ghost]) ?l:(st = (true : [%v: Node.t]))
    ?l:(en = (true : [%v: Node.t])) =
  { pre = rI s1 s2 c; res = (true : [%v: unit]); post = rI s1 s2 c }
