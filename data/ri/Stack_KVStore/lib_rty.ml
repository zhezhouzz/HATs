let[@libRty] putC ?l:(k = (true : [%v: Cell.t]))
    ?l:(next = (true : [%v: Cell.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutC ((k [@d]), (next [@d]), v, true);
  }

let[@libRty] putE ?l:(k = (true : [%v: Cell.t])) ?l:(a = (true : [%v: Elem.t]))
    =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutE ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] getC ((c : Cell.t) [@ghost]) ?l:(k = (true : [%v: Cell.t])) =
  {
    pre = storedCP k c;
    res = (v == c : [%v: Cell.t]);
    newadding = lastL && GetC ((k [@d]), v, v == c);
  }

let[@libRty] getE ((a : Elem.t) [@ghost]) ?l:(k = (true : [%v: Cell.t])) =
  {
    pre = storedEP k a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetE ((k [@d]), v, v == a);
  }

let[@libRty] existsC ?l:(k = (true : [%v: Cell.t])) =
  [|
    {
      pre = existsCP k;
      res = (v : [%v: bool]);
      newadding = lastL && ExistsC ((k [@d]), v, v);
    };
    {
      pre = not (existsCP k);
      res = (not v : [%v: bool]);
      newadding = lastL && ExistsC ((k [@d]), v, not v);
    };
  |]

let[@libRty] existsValC ?l:(k = (true : [%v: Cell.t])) =
  [|
    {
      pre = existsValCP k;
      res = (v : [%v: bool]);
      newadding = lastL && ExistsValC ((k [@d]), v, v);
    };
    {
      pre = not (existsValCP k);
      res = (not v : [%v: bool]);
      newadding = lastL && ExistsValC ((k [@d]), v, not v);
    };
  |]

let[@libRty] existsE ?l:(k = (true : [%v: Cell.t])) =
  [|
    {
      pre = existsEP k;
      res = (v : [%v: bool]);
      newadding = lastL && ExistsE ((k [@d]), v, v);
    };
    {
      pre = not (existsEP k);
      res = (not v : [%v: bool]);
      newadding = lastL && ExistsE ((k [@d]), v, not v);
    };
  |]

let[@libRty] newCell ?l:(k = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Cell.t]);
    newadding = lastL && NewCell (x_0, v, true);
  }
