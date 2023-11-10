let[@libRty] addNode ?l:(s = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Color.t])) =
  {
    pre = not (is_node s);
    res = (true : [%v: unit]);
    newadding = lastL && AddNode ((s [@d]), (c [@d]), v, true);
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

let[@libRty] getNodeColor ((c : Color.t) [@ghost])
    ?l:(s = (true : [%v: Node.t])) =
  {
    pre = node_has_color s c;
    res = (v == c : [%v: Color.t]);
    newadding = lastL && GetNodeColor ((s [@d]), v, v == c);
  }

let[@libRty] connect ?l:(s1 = (true : [%v: Node.t]))
    ?l:(s2 = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Connect ((s1 [@d]), (s2 [@d]), v, true);
  }

let[@libRty] disconnect ?l:(s1 = (true : [%v: Node.t]))
    ?l:(s2 = (true : [%v: Node.t])) =
  {
    pre = not (is_connected s1 s2);
    res = (true : [%v: unit]);
    newadding = lastL && Disconnect ((s1 [@d]), (s2 [@d]), v, true);
  }

let[@libRty] isConnected ?l:(s1 = (true : [%v: Node.t]))
    ?l:(s2 = (true : [%v: Node.t])) =
  [|
    {
      pre = is_connected s1 s2;
      res = (v : [%v: bool]);
      newadding = lastL && IsConnected ((s1 [@d]), (s2 [@d]), v, v);
    };
    {
      pre = not (is_connected s1 s2);
      res = (not v : [%v: bool]);
      newadding = lastL && IsConnected ((s1 [@d]), (s2 [@d]), v, not v);
    };
  |]
