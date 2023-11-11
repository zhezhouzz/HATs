let singleton (x : Node.t) : bool =
  if isNode x then false
  else (
    addNode x;
    connect x x;
    true)

let[@assertRty] singleton ((s1 : Node.t) [@ghost])
    ?l:(x = (true : [%v: Node.t])) =
  { pre = rI s1; res = (true : [%v: bool]); post = rI s1 }
