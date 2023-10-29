let[@assertSRLRty] rty1 ?l:(min = (true : [%v: int]))
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

let[@assertSRLRty] rty2 ?l:(min = (true : [%v: int]))
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
