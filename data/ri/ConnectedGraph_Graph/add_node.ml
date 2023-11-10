let add_node (old : Node.t) (x : Node.t) : bool =
  if isNode old then
    if isNode x then false
    else (
      addNode x;
      connect old x;
      true)
  else false

let[@assertRty] add_node ((s1 : Node.t) [@ghost])
    ?l:(old = (true : [%v: Node.t])) ?l:(x = (true : [%v: Node.t])) =
  { pre = rI s1; res = (true : [%v: bool]); post = rI s1 }
