let add_transition (st : Node.t) (en : Node.t) : unit =
  if is_node st then
    if is_node en then
      if mem st en then ()
      else (
        insert st en;
        ())
    else ()
  else ()

let[@libRty] is_node ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ?l:(x = (true : [%v: Node.t])) =
  [|
    {
      pre = rI s1 s2 && (mem_fstP x || mem_sndP x);
      res = (v : [%v: bool]);
      post = rI s1 s2 && (mem_fstP x || mem_sndP x);
    };
    {
      pre = rI s1 s2 && not (mem_fstP x || mem_sndP x);
      res = (not v : [%v: bool]);
      post = rI s1 s2 && not (mem_fstP x || mem_sndP x);
    };
  |]

let[@assertRty] add_transition ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ?l:(st = (true : [%v: Node.t])) ?l:(en = (true : [%v: Node.t])) =
  { pre = rI s1 s2; res = (true : [%v: unit]); post = rI s1 s2 }
