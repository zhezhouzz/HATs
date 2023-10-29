let[@libRty] put ?l:(k = (true : [%v: int])) ?l:(a = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] exists ?l:(k = (true : [%v: int])) =
  [|
    {
      pre = _F (Put ((k [@d]), x_1, v, true));
      res = (v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, v);
    };
    {
      pre = not (_F (Put ((k [@d]), x_1, v, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, not v);
    };
  |]

let[@libRty] get ((a : int) [@ghost]) ?l:(k = (true : [%v: int])) =
  {
    pre =
      _F
        (Put ((k [@d]), (a [@d]), v, true)
        && _X (_G (not (Put ((k [@d]), x_1, v, true)))));
    res = (v == a : [%v: int]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }
