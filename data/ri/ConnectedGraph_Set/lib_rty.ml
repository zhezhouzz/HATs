let[@libRty] insert ?l:(a = (true : [%v: Node.t]))
    ?l:(b = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Insert ((a [@d]), (b [@d]), v, true);
  }

let[@libRty] mem ?l:(a = (true : [%v: Node.t])) ?l:(b = (true : [%v: Node.t])) =
  [|
    {
      pre = memP a b;
      res = (v : [%v: bool]);
      newadding = lastL && Mem ((a [@d]), (b [@d]), v, v);
    };
    {
      pre = not (memP a b);
      res = (not v : [%v: bool]);
      newadding = lastL && Mem ((a [@d]), (b [@d]), v, not v);
    };
  |]

let[@libRty] memFst ?l:(a = (true : [%v: Node.t])) =
  [|
    {
      pre = mem_fstP a;
      res = (v : [%v: bool]);
      newadding = lastL && MemFst ((a [@d]), v, v);
    };
    {
      pre = not (mem_fstP a);
      res = (not v : [%v: bool]);
      newadding = lastL && MemFst ((a [@d]), v, not v);
    };
  |]

let[@libRty] memSnd ?l:(a = (true : [%v: Node.t])) =
  [|
    {
      pre = mem_sndP a;
      res = (v : [%v: bool]);
      newadding = lastL && MemSnd ((a [@d]), v, v);
    };
    {
      pre = not (mem_sndP a);
      res = (not v : [%v: bool]);
      newadding = lastL && MemSnd ((a [@d]), v, not v);
    };
  |]
