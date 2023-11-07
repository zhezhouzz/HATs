let new_thunk (x : unit) : unit = ()

let[@assertRty] new_thunk ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(y = (true : [%v: unit])) =
  { pre = rI i a; res = (true : [%v: unit]); post = rI i a }
