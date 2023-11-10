let force (thunk : unit -> unit) : unit =
  thunk ();
  ()

let[@assertRty] force
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI; res = (true : [%v: unit]); post = rI }) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
