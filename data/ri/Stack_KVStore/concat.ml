let rec concat (s1 : Cell.t) (s2 : Cell.t) : Cell.t =
  if existsValC s1 then s1
  else (
    concat_aux s1 s2;
    s1)

let[@libRty] concat_aux ((a : Cell.t) [@ghost]) ?l:(s1 = (true : [%v: Cell.t]))
    ?l:(s2 = (true : [%v: Cell.t])) =
  { pre = rI a; res = (true : [%v: unit]); post = rI a }

let[@assertRty] concat ((a : Cell.t) [@ghost]) ?l:(s1 = (true : [%v: Cell.t]))
    ?l:(s2 = (true : [%v: Cell.t])) =
  { pre = rI a; res = (true : [%v: Cell.t]); post = rI a }
