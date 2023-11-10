let del_transition (st : Node.t) (en : Node.t) : unit =
  if isNode st then
    if isNode en then
      if isConnected st en then
        if hasConnectIn en then
          if hasConnectOut st then (
            disconnect st en;
            ())
          else ()
        else ()
      else ()
    else ()
  else ()

let[@assertRty] del_transition ((s : Node.t) [@ghost])
    ?l:(st = (true : [%v: Node.t])) ?l:(en = (true : [%v: Node.t])) =
  { pre = rI s; res = (true : [%v: unit]); post = rI s }
