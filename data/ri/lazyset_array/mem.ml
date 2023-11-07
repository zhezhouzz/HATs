let rec lazy_mem (x : Elem.t) (thunk : unit -> unit) (z : unit) : bool =
  thunk ();
  let (res : bool) = mem_aux 0 x in
  res

let[@libRty] mem_aux ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(idx = (true : [%v: int])) ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI i a; res = (true : [%v: bool]); post = rI i a }

let[@assertRty] lazy_mem ((i : int) [@ghost]) ((a : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI i a; res = (true : [%v: unit]); post = rI i a })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI i a; res = (true : [%v: bool]); post = rI i a }
