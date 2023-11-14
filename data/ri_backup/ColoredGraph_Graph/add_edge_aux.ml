let add_edge_aux (st : Node.t) (en : Node.t) : unit =
  if isConnected st en then ()
  else
    let (c1 : Color.t) = getNodeColor st in
    let (c2 : Color.t) = getNodeColor en in
    if color_eq c1 c2 then ()
    else (
      connect st en;
      ())

let[@assertRty] add_edge_aux ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ((c : Color.t) [@ghost]) ?l:(st = (true : [%v: Node.t]))
    ?l:(en = (true : [%v: Node.t])) =
  {
    pre = rI s1 s2 c && is_node st && is_node en;
    res = (true : [%v: unit]);
    post = rI s1 s2 c;
  }