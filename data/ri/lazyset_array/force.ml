let force (thunk : unit -> unit) : unit =
  thunk ();
  ()

let[@assertRty] force ((m : Elem.t) [@ghost])
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI m; res = (true : [%v: unit]); post = rI m }) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
