let lazy_insert (x : Elem.t) (thunk : unit -> unit) (z : unit) : unit =
  thunk ();
  if exists x then ()
  else (
    put x ();
    ())

let[@assertRty] lazy_insert ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI m; res = (true : [%v: unit]); post = rI m })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
