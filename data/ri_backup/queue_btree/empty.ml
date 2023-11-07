let empty (u : unit) : unit = ()

let[@assertRty] empty ?l:(u = (true : [%v: unit])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
