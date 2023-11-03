(* multi-tree *)

let[@libRty] init ?l:(p1 = (true : [%v: Path.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Init ((p1 [@d]), v, true);
  }

let[@libRty] connect_child ?l:(p1 = (true : [%v: Path.t]))
    ?l:(p2 = (true : [%v: Path.t])) =
  {
    pre = memP p1;
    res = (true : [%v: unit]);
    newadding = lastL && Connect_child ((p1 [@d]), (p2 [@d]), v, true);
  }

let[@libRty] mem ?l:(k = (true : [%v: Path.t])) =
  [|
    {
      pre = memP k;
      res = (v : [%v: bool]);
      newadding = lastL && Mem ((k [@d]), v, v);
    };
    {
      pre = not (memP k);
      res = (not v : [%v: bool]);
      newadding = lastL && Mem ((k [@d]), v, not v);
    };
  |]

let[@libRty] put ?l:(k = (true : [%v: Path.t])) ?l:(a = (true : [%v: Bytes.t]))
    =
  {
    pre = memP k;
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] get ((a : Bytes.t) [@ghost]) ?l:(k = (true : [%v: Path.t])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: Bytes.t]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }
