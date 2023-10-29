let[@assertSRLRty] rty1 ?l:(min = (true : [%v: int]))
    ?l:(elem = (true : [%v: int])) =
  {
    pre =
      (starA (anyA - Setinsert (v0, v, min <= v0));
       Setinsert ((min [@d]), v, true);
       starA (anyA - Setinsert (v0, v, min < v0)));
    res = ((v == elem && elem <= min) || (v == min && elem > min) : [%v0: int]);
    newadding = Setinsert ((elem [@d]), v, true);
  }

let[@assertSRLRty] rty2 ?l:(min = (true : [%v: int]))
    ?l:(elem = (true : [%v: int])) =
  {
    pre =
      (starA (anyA - Setinsert (v0, v, min <= v0));
       Setinsert ((min [@d]), v, true);
       starA (anyA - Setinsert (v0, v, min < v0)));
    res = ((v == elem && elem <= min) || (v == min && elem > min) : [%v0: int]);
    newadding = Setinsert (v0, v, true);
  }
