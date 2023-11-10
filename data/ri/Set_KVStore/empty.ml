let rec empty (u : unit) : unit = ()

let[@assertRty] empty ((a : Elem.t) [@ghost]) ?l:(x = (true : [%v: unit])) =
  { pre = rI a; res = (true : [%v: unit]); post = rI a }
