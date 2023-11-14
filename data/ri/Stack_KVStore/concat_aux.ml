let rec concat_aux (s1 : Cell.t) (s2 : Cell.t) : unit =
  if existsC s1 then (
    let (s1' : Cell.t) = getC s1 in
    concat_aux s1' s2;
    ())
  else if existsValC s2 then ()
  else (
    putC s1 s2;
    ())

let[@assertRty] concat_aux ((a : Cell.t) [@ghost])
    ?l:(s1 = (true : [%v: Cell.t])) ?l:(s2 = (true : [%v: Cell.t])) =
  { pre = rI a; res = (true : [%v: unit]); post = rI a }
