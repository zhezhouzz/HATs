let new_thunk (x : unit) : unit = ()

let[@assertRty] new_thunk ((m : Elem.t) [@ghost]) ?l:(y = (true : [%v: unit])) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
