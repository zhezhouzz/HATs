let[@libRty] setHead ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetHead ((a [@d]), v, true);
  }

let[@libRty] hasHead ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre = _F (SetHead (x_0, v, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasHead (x_0, v, v);
    };
    {
      pre = not (_F (SetHead (x_0, v, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasHead (x_0, v, not v);
    };
  |]

let[@libRty] getHead ((a : Elem.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre = headP a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetHead (x_0, v, v == a);
  }

let[@libRty] setNext ?l:(prev = (true : [%v: Elem.t]))
    ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetNext ((prev [@d]), (a [@d]), v, true);
  }

let[@libRty] delNext ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = has_nextP a;
    res = (true : [%v: unit]);
    newadding = lastL && DelNext ((a [@d]), v, true);
  }

let[@libRty] getNext ((a : Elem.t) [@ghost]) ?l:(prev = (true : [%v: Elem.t])) =
  {
    pre = nextP prev a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetNext ((prev [@d]), v, v == a);
  }

let[@libRty] hasNext ?l:(a = (true : [%v: Elem.t])) =
  [|
    {
      pre = has_nextP a;
      res = (v : [%v: bool]);
      newadding = lastL && HasNext (x_0, v, v);
    };
    {
      pre = not (has_nextP a);
      res = (not v : [%v: bool]);
      newadding = lastL && HasNext (x_0, v, not v);
    };
  |]
