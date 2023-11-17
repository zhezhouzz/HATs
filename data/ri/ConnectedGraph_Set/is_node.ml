let is_node (x : Node.t) : bool =
  let (m1 : bool) = memFst x in
  if m1 then true
  else
    let (m2 : bool) = memSnd x in
    if m2 then true else false

let[@assertRty] is_node ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
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
