let add_node (x : Node.t) (color : Color.t) : bool =
  if isNode x then false
  else (
    addNode x color;
    true)

let[@assertRty] add_node ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ((c : Color.t) [@ghost]) ?l:(x = (true : [%v: Node.t]))
    ?l:(color = (true : [%v: Color.t])) =
  { pre = rI s1 s2 c; res = (true : [%v: bool]); post = rI s1 s2 c }
