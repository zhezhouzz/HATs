let lazy_mem (x : Elem.t) (thunk : unit -> unit) (z : unit) : bool =
  thunk ();
  let (res : bool) = mem x in
  res

let[@assertRty] lazy_mem ((m : Elem.t) [@ghost]) ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI m; res = (true : [%v: unit]); post = rI m })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI m; res = (true : [%v: bool]); post = rI m }
