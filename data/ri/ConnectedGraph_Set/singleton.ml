let singleton (x : Node.t) : bool =
  if is_node x then false
  else (
    insert x x;
    true)

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

let[@assertRty] singleton ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ?l:(x = (true : [%v: Node.t])) =
  { pre = rI s1 s2; res = (true : [%v: bool]); post = rI s1 s2 }
