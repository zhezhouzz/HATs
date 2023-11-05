let[@libRty] put_root ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put_root ((a [@d]), v, true);
  }

let[@libRty] add_left ?l:(a = (true : [%v: Elem.t]))
    ?l:(b = (true : [%v: Elem.t])) =
  {
    pre = memP a && not (has_leftP a);
    res = (true : [%v: unit]);
    newadding = lastL && Add_left ((a [@d]), (b [@d]), v, true);
  }

let[@libRty] add_right ?l:(a = (true : [%v: Elem.t]))
    ?l:(b = (true : [%v: Elem.t])) =
  {
    pre = memP a && not (has_leftP a);
    res = (true : [%v: unit]);
    newadding = lastL && Add_left ((a [@d]), (b [@d]), v, true);
  }

let[@libRty] has_root ?l:(a = (true : [%v: unit])) =
  [|
    {
      pre = _F (Put_root (x_0, v, true));
      res = (v : [%v: bool]);
      newadding = lastL && Has_root (x_0, v, v);
    };
    {
      pre = not (_F (Put_root (x_0, v, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && Has_root (x_0, v, not v);
    };
  |]

let[@libRty] has_left ?l:(a = (true : [%v: Elem.t])) =
  [|
    {
      pre = has_leftP a;
      res = (v : [%v: bool]);
      newadding = lastL && Has_left ((a [@d]), v, v);
    };
    {
      pre = not (has_leftP a);
      res = (not v : [%v: bool]);
      newadding = lastL && Has_left ((a [@d]), v, not v);
    };
  |]

let[@libRty] has_right ?l:(a = (true : [%v: Elem.t])) =
  [|
    {
      pre = has_rightP a;
      res = (v : [%v: bool]);
      newadding = lastL && Has_right ((a [@d]), v, v);
    };
    {
      pre = not (has_rightP a);
      res = (not v : [%v: bool]);
      newadding = lastL && Has_right ((a [@d]), v, not v);
    };
  |]

let[@libRty] get_root ((a : Elem.t) [@ghost]) ?l:(b = (true : [%v: unit])) =
  {
    pre = _F (Put_root ((a [@d]), v, true));
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && Get_root (x_0, v, v == a);
  }

let[@libRty] get_left ((a : Elem.t) [@ghost]) ?l:(b = (true : [%v: Elem.t])) =
  {
    pre = _F (Add_left ((b [@d]), (a [@d]), v, true));
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && Get_left ((b [@d]), v, v == a);
  }

let[@libRty] get_right ((a : Elem.t) [@ghost]) ?l:(b = (true : [%v: Elem.t])) =
  {
    pre = _F (Add_right ((b [@d]), (a [@d]), v, true));
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && Get_right ((b [@d]), v, v == a);
  }

(* let[@libRty] mem ?l:(a = (true : [%v: Elem.t])) = *)
(*   [| *)
(*     { *)
(*       pre = memP a; *)
(*       res = (v : [%v: bool]); *)
(*       newadding = lastL && Mem ((a [@d]), v, v); *)
(*     }; *)
(*     { *)
(*       pre = not (memP a); *)
(*       res = (not v : [%v: bool]); *)
(*       newadding = lastL && Mem ((a [@d]), v, not v); *)
(*     }; *)
(*   |] *)
