let[@pred] storedP (k : int) (value : int) =
  _F
    (Put ((k [@d]), (value [@d]), v, true)
    && _X (_G (not (Put ((k [@d]), x_1, v, true)))))

let[@pred] existsP (k : int) = _F (Put ((k [@d]), x_1, v, true))

let[@libRty] put ?l:(k = (true : [%v: int])) ?l:(a = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] exists ?l:(k = (true : [%v: int])) =
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

let[@libRty] get ((a : int) [@ghost]) ?l:(k = (true : [%v: int])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: int]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }
