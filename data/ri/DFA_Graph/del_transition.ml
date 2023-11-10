let del_transition (st : Node.t) (ch : Char.t) (en : Node.t) : unit =
  if isNode st then
    if isNode en then
      if isConnected st ch en then (
        disconnect st ch en;
        ())
      else ()
    else ()
  else ()

let[@assertRty] del_transition ((s1 : Node.t) [@ghost]) ((c : Char.t) [@ghost])
    ?l:(st = (true : [%v: Node.t])) ?l:(ch = (true : [%v: Char.t]))
    ?l:(en = (true : [%v: Node.t])) =
  { pre = rI s1 c; res = (true : [%v: unit]); post = rI s1 c }
