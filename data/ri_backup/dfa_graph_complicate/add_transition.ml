let add_transition (st : Node.t) (ch : Char.t) (en : Node.t) : unit =
  if isNode st then
    if isNode en then
      if hasOutEdge st ch then ()
      else (
        connect st ch en;
        ())
    else ()
  else ()

let[@assertRty] add_transition ((s1 : Node.t) [@ghost]) ((c : Char.t) [@ghost])
    ((s2 : Node.t) [@ghost]) ?l:(st = (true : [%v: Node.t]))
    ?l:(ch = (true : [%v: Char.t])) ?l:(en = (true : [%v: Node.t])) =
  { pre = rI s1 c s2; res = (true : [%v: unit]); post = rI s1 c s2 }
