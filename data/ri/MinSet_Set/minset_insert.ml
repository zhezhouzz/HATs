let minset_insert (x : Elem.t) : unit =
  if isWritten () then
    let (min : Elem.t) = read () in
    if elem_lt x min then (
      write x;
      insert x;
      ())
    else (
      insert x;
      ())
  else (
    write x;
    insert x;
    ())

let minset_insert (x : Elem.t) : unit =
  (if not (isWritten ()) then write x (* if empty, then update min element *)
   else
     let (min : Elem.t) = read () in
     (* if not empty, read min element *)
     if elem_lt x min then write x);
  (* is input element is smaller, update min element *)
  insert x (* always insert input element *)

let[@assertRty] minset_insert ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
