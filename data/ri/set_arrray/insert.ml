let rec insert (x : Elem.t) : unit =
  let (idx : int) = read () in
  let (len : int) = size () in
  if idx < len then (
    update idx x;
    write (idx + 1);
    ())
  else ()

let[@assertRty] insert ((n : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI n a; res = (true : [%v: unit]); post = rI n a }
