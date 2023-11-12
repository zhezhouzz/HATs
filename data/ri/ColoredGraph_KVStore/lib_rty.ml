let[@libRty] putC ?l:(k = (true : [%v: Node.t])) ?l:(a = (true : [%v: Color.t]))
    =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutC ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] getC ((a : Color.t) [@ghost]) ?l:(k = (true : [%v: Node.t])) =
  {
    pre = storedCP k a;
    res = (v == a : [%v: Color.t]);
    newadding = lastL && GetC ((k [@d]), v, v == a);
  }

let[@libRty] existsC ?l:(k = (true : [%v: Node.t])) =
  [|
    {
      pre = existsCP k;
      res = (v : [%v: bool]);
      newadding = lastL && ExistsC ((k [@d]), v, v);
    };
    {
      pre = not (existsCP k);
      res = (not v : [%v: bool]);
      newadding = lastL && ExistsC ((k [@d]), v, not v);
    };
  |]

let[@libRty] putE ?l:(k = (true : [%v: Node.t])) ?l:(a = (true : [%v: Node.t]))
    =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutE ((k [@d]), (a [@d]), v, true);
  }

(* let[@libRty] delE ?l:(k = (true : [%v: Node.t])) ?l:(a = (true : [%v: Node.t])) *)
(*     = *)
(*   { *)
(*     pre = existsEP k a; *)
(*     res = (true : [%v: unit]); *)
(*     newadding = lastL && DelE ((k [@d]), (a [@d]), v, true); *)
(*   } *)

let[@libRty] existsE ?l:(k = (true : [%v: Node.t]))
    ?l:(a = (true : [%v: Node.t])) =
  [|
    {
      pre = existsEP k a;
      res = (v : [%v: bool]);
      newadding = lastL && ExistsE ((k [@d]), (a [@d]), v, v);
    };
    {
      pre = not (existsEP k a);
      res = (not v : [%v: bool]);
      newadding = lastL && ExistsE ((k [@d]), (a [@d]), v, not v);
    };
  |]
