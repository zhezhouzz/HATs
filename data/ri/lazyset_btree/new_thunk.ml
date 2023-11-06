let new_thunk (x : unit) : unit = ()

let[@assertRty] new_thunk ?l:(y = (true : [%v: unit])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
