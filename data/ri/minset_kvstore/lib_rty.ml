let[@libRty] put ?l:(k = (true : [%v: Key.t])) ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] get ((a : Elem.t) [@ghost]) ?l:(k = (true : [%v: Key.t])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }

let[@libRty] exists ?l:(k = (true : [%v: Key.t])) =
  [|
    {
      pre = existsP k;
      res = (v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, v);
    };
    {
      pre = not (existsP k);
      res = (not v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, not v);
    };
  |]

let[@libRty] hasValue ?l:(a = (true : [%v: Elem.t])) =
  [|
    {
      pre = has_valueP a;
      res = (v : [%v: bool]);
      newadding = lastL && HasValue ((a [@d]), v, v);
    };
    {
      pre = not (has_valueP a);
      res = (not v : [%v: bool]);
      newadding = lastL && HasValue ((a [@d]), v, not v);
    };
  |]

let[@libRty] randomKey ?l:(k = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Key.t]);
    newadding = lastL && RandomKey (x_0, v, true);
  }

let[@libRty] write ?l:(idx = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Write ((idx [@d]), v, true);
  }

let[@libRty] read ((a : Elem.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre = writtenP a;
      res = (v == a : [%v: Elem.t]);
      newadding = lastL && Read (x_0, v, v == a);
    };
  |]

let[@libRty] isWritten ((a : Elem.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre = writtenP a;
      res = (v : [%v: bool]);
      newadding = lastL && IsWritten (x_0, v, v);
    };
    {
      pre = not (writtenP a);
      res = (not v : [%v: bool]);
      newadding = lastL && IsWritten (x_0, v, not v);
    };
  |]
