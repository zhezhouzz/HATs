(* set *)

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
