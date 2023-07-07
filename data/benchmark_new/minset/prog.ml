type effect = Setinsert of (int -> unit) | Setmem of (int -> bool)

let min_insert (min : int) (elem : int) : int =
  if elem < min then
    let (dummy1 : unit) = perform (Setinsert elem) in
    elem
  else
    let (dummy2 : unit) = perform (Setinsert elem) in
    min

let[@assert] min_insert ?l:(min = (true : [%v: int]))
    ?l:(elem = (true : [%v: int])) =
  {
    pre =
      (starA (anyA - Setinsert ((min <= v0 : [%v0: int]) : [%v: unit]));
       Setinsert (min, (true : [%v: unit]));
       starA (anyA - Setinsert ((min < v0 : [%v0: int]) : [%v: unit])));
    post =
      ((Setinsert (elem, (true : [%v: unit]));
        Ret
          ((v == elem && elem <= min) || (v == min && elem > min) : [%v0: int])) : 
      int);
  }
