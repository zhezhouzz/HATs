let[@effrty] put ?l:(k = (true : [%v: nat])) ?l:(va = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    post = lastL && Put ((k [@d]), (va [@d]), v, true);
  }
