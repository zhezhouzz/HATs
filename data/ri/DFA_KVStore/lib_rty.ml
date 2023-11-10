let[@libRty] put ?l:(a = (true : [%v: Node.t])) ?l:(c = (true : [%v: Char.t]))
    ?l:(b = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((a [@d]), (c [@d]), (b [@d]), v, true);
  }

let[@libRty] get ((b : Node.t) [@ghost]) ?l:(a = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) =
  {
    pre = storedP a c b;
    res = (v == b : [%v: Node.t]);
    newadding = lastL && Get ((a [@d]), (c [@d]), v, v == b);
  }

let[@libRty] exists ?l:(a = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) =
  [|
    {
      pre = existsP a c;
      res = (v : [%v: bool]);
      newadding = lastL && Exists ((a [@d]), (c [@d]), v, v);
    };
    {
      pre = not (existsP a c);
      res = (not v : [%v: bool]);
      newadding = lastL && Exists ((a [@d]), (c [@d]), v, not v);
    };
  |]

let[@libRty] del ?l:(a = (true : [%v: Node.t])) ?l:(c = (true : [%v: Char.t])) =
  {
    pre = existsP a c;
    res = (true : [%v: unit]);
    newadding = lastL && Del ((a [@d]), (c [@d]), v, true);
  }
