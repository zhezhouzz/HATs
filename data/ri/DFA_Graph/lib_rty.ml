let[@libRty] addNode ?l:(s = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && AddNode ((s [@d]), v, true);
  }

let[@libRty] isNode ?l:(s = (true : [%v: Node.t])) =
  [|
    {
      pre = is_node s;
      res = (v : [%v: bool]);
      newadding = lastL && IsNode ((s [@d]), v, v);
    };
    {
      pre = not (is_node s);
      res = (not v : [%v: bool]);
      newadding = lastL && IsNode ((s [@d]), v, not v);
    };
  |]

let[@libRty] connect ?l:(s1 = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) ?l:(s2 = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Connect ((s1 [@d]), (c [@d]), (s2 [@d]), v, true);
  }

let[@libRty] disconnect ?l:(s1 = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) ?l:(s2 = (true : [%v: Node.t])) =
  {
    pre = not (is_trans s1 c s2);
    res = (true : [%v: unit]);
    newadding = lastL && Disconnect ((s1 [@d]), (c [@d]), (s2 [@d]), v, true);
  }

let[@libRty] isConnected ?l:(s1 = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) ?l:(s2 = (true : [%v: Node.t])) =
  [|
    {
      pre = is_trans s1 c s2;
      res = (v : [%v: bool]);
      newadding = lastL && IsConnected ((s1 [@d]), (c [@d]), (s2 [@d]), v, v);
    };
    {
      pre = not (is_trans s1 c s2);
      res = (not v : [%v: bool]);
      newadding = lastL && IsConnected ((s1 [@d]), (c [@d]), (s2 [@d]), v, not v);
    };
  |]

let[@libRty] hasOutEdge ?l:(s1 = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) =
  [|
    {
      pre = has_out_edge s1 c;
      res = (v : [%v: bool]);
      newadding = lastL && HasOutEdge ((s1 [@d]), (c [@d]), v, v);
    };
    {
      pre = not (has_out_edge s1 c);
      res = (not v : [%v: bool]);
      newadding = lastL && HasOutEdge ((s1 [@d]), (c [@d]), v, not v);
    };
  |]
