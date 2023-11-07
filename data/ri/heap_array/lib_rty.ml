let[@libRty] init ?l:(n = (true : [%v: int])) =
  {
    pre = not (_F (Init (x_0, v, true)));
    res = (true : [%v: unit]);
    newadding = lastL && Init ((n [@d]), v, true);
  }

let[@libRty] isInited ?l:(n = (true : [%v: unit])) =
  [|
    {
      pre = _F (Init (x_0, v, true));
      res = (v : [%v: bool]);
      newadding = lastL && IsInited (x_0, v, v);
    };
    {
      pre = not (_F (Init (x_0, v, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && IsInited (x_0, v, not v);
    };
  |]

let[@libRty] size ((n : int) [@ghost]) ?l:(y = (true : [%v: unit])) =
  {
    pre = sizeP n;
    res = (v == n : [%v: int]);
    newadding = lastL && Size (x_0, v, v == n);
  }

let[@libRty] update ?l:(idx = (true : [%v: int])) ?l:(a = (true : [%v: Elem.t]))
    =
  {
    pre = valid_idxP idx;
    res = (true : [%v: unit]);
    newadding = lastL && Update ((idx [@d]), (a [@d]), v, true);
  }

let[@libRty] select ((a : Elem.t) [@ghost]) ?l:(idx = (true : [%v: int])) =
  [|
    {
      pre = storedP idx a;
      res = (v == a : [%v: Elem.t]);
      newadding = lastL && Select ((idx [@d]), v, v == a);
    };
    {
      pre = not (existsP idx);
      res = (true : [%v: Elem.t]);
      newadding = lastL && Select ((idx [@d]), v, true);
    };
  |]

let[@libRty] randomLen ?l:(a = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (0 < v : [%v: int]);
    newadding = lastL && RandomLen (x_0, v, 0 < v);
  }
