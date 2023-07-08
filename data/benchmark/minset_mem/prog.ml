type effect =
  | Setinsert of (int -> unit)
  (* | SetDel of (int -> unit) *)
  | Setmem of (int -> bool)
(* | ReadAddr of (nat -> int) *)
(* | WriteAddr of (nat -> int -> unit) *)

(* A set equips with a min and max *)

let min_mem (min : int) (elem : int) : bool =
  if elem < min then false
  else if elem == min then true
  else
    let (res : bool) = perform (Setmem elem) in
    res

let[@assert] min_mem ?l:(min = (true : [%v: int]))
    ?l:(elem = (true : [%v: int])) =
  {
    pre =
      (starA (anyA - Setinsert ((min <= v0 : [%v0: int]) : [%v: unit]));
       Setinsert (min, (true : [%v: unit]));
       starA (anyA - Setinsert ((min < v0 : [%v0: int]) : [%v: unit])));
    post =
      (Ret ((not v0) && elem < min : [%v0: bool])
       || Ret (v0 && elem == min : [%v0: bool])
       ||
       (Setmem (elem, (true : [%v: bool]));
        Ret (elem > min : [%v0: bool])) : bool);
  }
