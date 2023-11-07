(* set *)

let[@libRty] insert ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Insert ((a [@d]), v, true);
  }

let[@libRty] mem ?l:(a = (true : [%v: Elem.t])) =
  [|
    {
      pre = memP a;
      res = (v : [%v: bool]);
      newadding = lastL && Mem ((a [@d]), v, v);
    };
    {
      pre = not (memP a);
      res = (not v : [%v: bool]);
      newadding = lastL && Mem ((a [@d]), v, not v);
    };
  |]

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
