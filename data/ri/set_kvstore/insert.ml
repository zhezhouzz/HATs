let rec insert (x : Elem.t) : unit =
  if hasValue x then ()
  else
    let (k : Key.t) = randomKey () in
    if exists k then (
      insert x;
      ())
    else (
      put k x;
      ())

let[@assertRty] insert ((a : Elem.t) [@ghost]) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI a; res = (true : [%v: unit]); post = rI a }
