type effect =
  | Matread of (int -> int -> int)
  | Matwrite of (int -> int -> int -> unit)

(* There are three tables for a graph *)
(* mat: vid -> vid -> bool *)

let rec delete_edge (a : int) (b : int) : unit =
  if a == b then
    let (dummy1 : unit) = perform (Matwrite (a, b, 0)) in
    ()
  else
    let (dummy1 : unit) = perform (Matwrite (a, b, 0)) in
    let (dummy2 : unit) = perform (Matwrite (b, a, 0)) in
    ()

let[@assert] delete_edge ?l:(a = (true : [%v: int]))
    ?l:(b = (a <= v : [%v: int])) =
  {
    pre =
      (starA anyA;
       Matwrite
         ( a,
           ((((not (v1 == b)) && v2 > 0 : [%v1: int]) : [%v2: int])
             : [%v: unit]) );
       starA
         (anyA
         - Matwrite
             ((((v0 != a : [%v0: int]) : [%v1: int]) : [%v2: int]) : [%v: unit])
         );
       Matwrite
         (((((not (v0 == a)) && v1 == b && v2 > 0 : [%v0: int]) : [%v1: int])
            : [%v2: int])
           : [%v: unit]);
       starA
         (anyA
         - Matwrite
             ((((v0 != a || v1 != b : [%v0: int]) : [%v1: int]) : [%v2: int])
               : [%v: unit])));
    post =
      ((starA
          (anyA
          - Matwrite
              ((((true : [%v0: int]) : [%v1: int]) : [%v2: int]) : [%v: unit]));
        Matwrite (a, b, ((v2 <= 0 : [%v2: int]) : [%v: unit]));
        starA (Matwrite (b, a, ((v2 <= 0 : [%v2: int]) : [%v: unit])));
        Ret (true : [%v0: unit])) : unit);
  }
