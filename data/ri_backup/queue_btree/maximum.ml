let rec maximum (default : Elem.t) : Elem.t =
  if has_root () then
    let (root : Elem.t) = get_root () in
    root
  else default

let[@assertRty] maximum ?l:(default = (true : [%v: Elem.t])) =
  { pre = rI; res = (true : [%v: Elem.t]); post = rI }
