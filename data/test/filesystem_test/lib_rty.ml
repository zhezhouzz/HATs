(* kvstore *)

let[@libRty] put ?l:(k = (true : [%v: Path.t])) ?l:(a = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] exists ?l:(k = (true : [%v: Path.t])) =
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

let[@libRty] get ((a : int) [@ghost]) ?l:(k = (true : [%v: Path.t])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: int]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }
