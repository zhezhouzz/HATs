(* kvstore *)

let[@libRty] put ?l:(k = (true : [%v: Elem.t])) ?l:(a = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), x_1, v, true);
  }

let[@libRty] exists ?l:(k = (true : [%v: Elem.t])) =
  [|
    {
      pre = memP k;
      res = (v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, v);
    };
    {
      pre = not (memP k);
      res = (not v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, not v);
    };
  |]
