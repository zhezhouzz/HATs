let insert (x : Elem.t) : unit =
  insert_aux 0 x;
  ()

let[@libRty] insert_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(idx = (true : [%v: int])) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }

let[@assertRty] insert ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }
