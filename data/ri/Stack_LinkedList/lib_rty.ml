let[@libRty] newCell ((x : Cell.t) [@ghost]) ?l:(a = (true : [%v: unit])) =
  {
    pre = _G (not (NewCell (x_0, v, v == x)));
    res = (v == x : [%v: Cell.t]);
    newadding = lastL && NewCell (x_0, v, v == x);
  }

let[@libRty] isCell ?l:(c = (true : [%v: Cell.t])) =
  [|
    {
      pre = is_cell c;
      res = (v : [%v: bool]);
      newadding = lastL && IsCell (x_0, v, v);
    };
    {
      pre = not (is_cell c);
      res = (not v : [%v: bool]);
      newadding = lastL && IsCell (x_0, v, not v);
    };
  |]

let[@libRty] putCellContent ?l:(c = (true : [%v: Cell.t]))
    ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = is_cell c;
    res = (true : [%v: unit]);
    newadding = lastL && PutCellContent ((c [@d]), (a [@d]), v, true);
  }

let[@libRty] hasCellContent ?l:(c = (true : [%v: Cell.t])) =
  [|
    {
      pre = is_storedP c;
      res = (v : [%v: bool]);
      newadding = lastL && HasCellContent (x_0, v, v);
    };
    {
      pre = not (is_storedP c);
      res = (not v : [%v: bool]);
      newadding = lastL && HasCellContent (x_0, v, not v);
    };
  |]

let[@libRty] getCellContent ((a : Elem.t) [@ghost])
    ?l:(c = (true : [%v: Cell.t])) =
  {
    pre = storeP c a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetCellContent ((c [@d]), v, v == a);
  }

let[@libRty] setNext ?l:(prev = (true : [%v: Cell.t]))
    ?l:(a = (true : [%v: Cell.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetNext ((prev [@d]), (a [@d]), v, true);
  }

let[@libRty] getNext ((a : Cell.t) [@ghost]) ?l:(prev = (true : [%v: Cell.t])) =
  {
    pre = nextP prev a;
    res = (v == a : [%v: Cell.t]);
    newadding = lastL && GetNext ((prev [@d]), v, v == a);
  }

let[@libRty] hasNext ?l:(a = (true : [%v: Cell.t])) =
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

let[@libRty] hasPrev ?l:(a = (true : [%v: Cell.t])) =
  [|
    {
      pre = has_prevP a;
      res = (v : [%v: bool]);
      newadding = lastL && HasPrev (x_0, v, v);
    };
    {
      pre = not (has_prevP a);
      res = (not v : [%v: bool]);
      newadding = lastL && HasPrev (x_0, v, not v);
    };
  |]
