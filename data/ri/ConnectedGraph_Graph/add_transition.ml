let add_transition (st : Node.t) (en : Node.t) : unit =
  if isNode st then
    if isNode en then
      if isConnected st en then ()
      else (
        connect st en;
        ())
    else ()
  else ()

let[@assertRty] add_transition ((s : Node.t) [@ghost])
    ?l:(st = (true : [%v: Node.t])) ?l:(en = (true : [%v: Node.t])) =
  { pre = rI s; res = (true : [%v: unit]); post = rI s }
