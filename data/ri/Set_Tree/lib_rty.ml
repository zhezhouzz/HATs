let[@libRty] putRoot ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutRoot ((a [@d]), v, true);
  }

let[@libRty] addLeft ?l:(a = (true : [%v: Elem.t]))
    ?l:(b = (true : [%v: Elem.t])) =
  {
    pre = memP a && not (has_leftP a);
    res = (true : [%v: unit]);
    newadding = lastL && AddLeft ((a [@d]), (b [@d]), v, true);
  }

let[@libRty] addRight ?l:(a = (true : [%v: Elem.t]))
    ?l:(b = (true : [%v: Elem.t])) =
  {
    pre = memP a && not (has_leftP a);
    res = (true : [%v: unit]);
    newadding = lastL && AddRight ((a [@d]), (b [@d]), v, true);
  }

let[@libRty] hasRoot ?l:(a = (true : [%v: unit])) =
  [|
    {
      pre = _F (PutRoot (x_0, v, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasRoot (x_0, v, v);
    };
    {
      pre = not (_F (PutRoot (x_0, v, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasRoot (x_0, v, not v);
    };
  |]

let[@libRty] hasLeft ?l:(a = (true : [%v: Elem.t])) =
  [|
    {
      pre = has_leftP a;
      res = (v : [%v: bool]);
      newadding = lastL && HasLeft ((a [@d]), v, v);
    };
    {
      pre = not (has_leftP a);
      res = (not v : [%v: bool]);
      newadding = lastL && HasLeft ((a [@d]), v, not v);
    };
  |]

let[@libRty] hasRight ?l:(a = (true : [%v: Elem.t])) =
  [|
    {
      pre = has_rightP a;
      res = (v : [%v: bool]);
      newadding = lastL && HasRight ((a [@d]), v, v);
    };
    {
      pre = not (has_rightP a);
      res = (not v : [%v: bool]);
      newadding = lastL && HasRight ((a [@d]), v, not v);
    };
  |]

let[@libRty] getRoot ((a : Elem.t) [@ghost]) ?l:(b = (true : [%v: unit])) =
  {
    pre = _F (PutRoot ((a [@d]), v, true));
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetRoot (x_0, v, v == a);
  }

let[@libRty] getLeft ((a : Elem.t) [@ghost]) ?l:(b = (true : [%v: Elem.t])) =
  {
    pre = _F (AddLeft ((b [@d]), (a [@d]), v, true));
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetLeft ((b [@d]), v, v == a);
  }

let[@libRty] getRight ((a : Elem.t) [@ghost]) ?l:(b = (true : [%v: Elem.t])) =
  {
    pre = _F (AddRight ((b [@d]), (a [@d]), v, true));
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetRight ((b [@d]), v, v == a);
  }
