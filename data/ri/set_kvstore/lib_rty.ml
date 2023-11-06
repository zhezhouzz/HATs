let[@libRty] put ?l:(k = (true : [%v: Key.t])) ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] get ((a : Elem.t) [@ghost]) ?l:(k = (true : [%v: Key.t])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }

let[@libRty] exists ?l:(k = (true : [%v: Key.t])) =
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

let[@libRty] has_value ?l:(a = (true : [%v: Elem.t])) =
  [|
    {
      pre = has_valueP a;
      res = (v : [%v: bool]);
      newadding = lastL && Has_value ((a [@d]), v, v);
    };
    {
      pre = not (has_valueP a);
      res = (not v : [%v: bool]);
      newadding = lastL && Has_value ((a [@d]), v, not v);
    };
  |]

let[@libRty] random_key ?l:(k = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Key.t]);
    newadding = lastL && Random_key (x_0, v, true);
  }
