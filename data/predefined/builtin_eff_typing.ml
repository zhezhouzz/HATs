(* kvstore *)

let[@libRty] put ?l:(k = (true : [%v: Path.t])) ?l:(a = (true : [%v: Bytes.t]))
    =
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

let[@libRty] get ((a : Bytes.t) [@ghost]) ?l:(k = (true : [%v: Path.t])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: Bytes.t]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }

(* multi-tree *)

let[@libRty] mtree_init ?l:(p1 = (true : [%v: Path.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Mtree_init ((p1 [@d]), v, true);
  }

let[@libRty] mtree_add_child ?l:(p1 = (true : [%v: Path.t]))
    ?l:(p2 = (true : [%v: Path.t])) =
  {
    pre = mtree_memP p1;
    res = (true : [%v: unit]);
    newadding = lastL && Mtree_add_child ((p1 [@d]), (p2 [@d]), v, true);
  }

let[@libRty] mtree_mem ?l:(k = (true : [%v: Path.t])) =
  [|
    {
      pre = mtree_memP k;
      res = (v : [%v: bool]);
      newadding = lastL && Mtree_mem ((k [@d]), v, v);
    };
    {
      pre = not (mtree_memP k);
      res = (not v : [%v: bool]);
      newadding = lastL && Mtree_mem ((k [@d]), v, not v);
    };
  |]

let[@libRty] mtree_put ?l:(k = (true : [%v: Path.t]))
    ?l:(a = (true : [%v: Bytes.t])) =
  {
    pre = mtree_memP k;
    res = (true : [%v: unit]);
    newadding = lastL && Mtree_put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] mtree_get ((a : Bytes.t) [@ghost]) ?l:(k = (true : [%v: Path.t])) =
  {
    pre = mtree_storedP k a;
    res = (v == a : [%v: Bytes.t]);
    newadding = lastL && Mtree_get ((k [@d]), v, v == a);
  }
