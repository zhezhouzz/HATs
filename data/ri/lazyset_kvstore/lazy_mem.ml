let rec mem (x : Elem.t) (thunk : unit -> unit) (z : unit) : bool =
  thunk ();
  let (res : bool) = hasValue x in
  res

let[@assertRty] mem ((a : Elem.t) [@ghost]) ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI a; res = (true : [%v: unit]); post = rI a })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI a; res = (true : [%v: bool]); post = rI a }
