let[@libRty] newNode ((x : Node.t) [@ghost]) ?l:(a = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (v == x : [%v: Node.t]);
    newadding = lastL && NewNode (x_0, v, v == x);
  }

let[@libRty] putNodeContent ?l:(s = (true : [%v: Node.t]))
    ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutNodeContent ((s [@d]), (a [@d]), v, true);
  }

let[@libRty] hasNodeContent ?l:(s = (true : [%v: Node.t])) =
  [|
    {
      pre = is_node s;
      res = (v : [%v: bool]);
      newadding = lastL && HasNodeContent ((s [@d]), v, v);
    };
    {
      pre = not (is_node s);
      res = (not v : [%v: bool]);
      newadding = lastL && HasNodeContent ((s [@d]), v, not v);
    };
  |]

let[@libRty] getNodeContent ((a : Elem.t) [@ghost])
    ?l:(c = (true : [%v: Node.t])) =
  {
    pre = storeP c a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetNodeContent ((c [@d]), v, v == a);
  }

let[@libRty] connect ?l:(s1 = (true : [%v: Node.t]))
    ?l:(s2 = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Connect ((s1 [@d]), (s2 [@d]), v, true);
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

let[@libRty] hasConnectIn ?l:(s = (true : [%v: Node.t])) =
  [|
    {
      pre = has_connect_in s;
      res = (v : [%v: bool]);
      newadding = lastL && HasConnectIn ((s [@d]), v, v);
    };
    {
      pre = not (has_connect_in s);
      res = (not v : [%v: bool]);
      newadding = lastL && HasConnectIn ((s [@d]), v, not v);
    };
  |]

let[@libRty] hasConnectOut ?l:(s = (true : [%v: Node.t])) =
  [|
    {
      pre = has_connect_out s;
      res = (v : [%v: bool]);
      newadding = lastL && HasConnectOut ((s [@d]), v, v);
    };
    {
      pre = not (has_connect_out s);
      res = (not v : [%v: bool]);
      newadding = lastL && HasConnectOut ((s [@d]), v, not v);
    };
  |]
