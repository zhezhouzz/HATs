type effect =
  | Addvertex of (int -> int -> unit)
  | Connectvertices of (int -> int -> unit)
  | Isvertex of (int -> bool)
  | Getvertexval of (int -> int)
  | Isconnected of (int -> int -> bool)

let add_colored_vertice (a : int) (b : int) (bc : int) : unit =
  if perform (Isvertex a) then
    if perform (Isvertex b) then ()
    else if perform (Getvertexval a) == bc then ()
    else if perform (Isconnected (a, b)) then ()
    else
      let (dummy0 : unit) = perform (Addvertex (b, bc)) in
      let (dummy1 : unit) = perform (Connectvertices (a, b)) in
      ()
  else ()

let[@assert] add_colored_vertice ?l:(a = (true : [%v: int]))
    ?l:(b = (not (v == a) : [%v: int])) ?l:(bc = (true : [%v: int])) =
  {
    pre =
      (starA
         (anyA
         - Addvertex (b, ((true : [%v1: int]) : [%v: unit]))
         - Connectvertices (a, b, (true : [%v: unit])));
       Addvertex (a, ((not (v1 == bc) : [%v1: int]) : [%v: unit]));
       starA
         (anyA
         - Connectvertices (a, b, (true : [%v: unit]))
         - Addvertex (a, ((true : [%v1: int]) : [%v: unit]))
         - Addvertex (b, ((true : [%v1: int]) : [%v: unit]))));
    post =
      ((starA
          (anyA
          - Addvertex (((true : [%v0: int]) : [%v1: int]) : [%v: unit])
          - Connectvertices (((true : [%v0: int]) : [%v1: int]) : [%v: unit]));
        Addvertex (b, bc, (true : [%v: unit]));
        Connectvertices (a, b, (true : [%v: unit]));
        Ret (true : [%v0: unit])) : unit);
  }
