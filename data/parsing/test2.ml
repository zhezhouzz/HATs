let[@libSRLRty] put ?l:(k = (true : [%v: int])) ?l:(a = (true : [%v: int])) =
  {
    pre = starA anyA;
    res = (true : [%v: unit]);
    newadding = Put ((k [@d]), (a [@d]), v, true);
  }

let[@libSRLRty] exists ?l:(k = (true : [%v: int])) =
  [|
    {
      pre =
        (starA anyA;
         Put ((k [@d]), x_1, v, true);
         starA anyA);
      res = (v : [%v: bool]);
      newadding = Exists ((k [@d]), v, v);
    };
    {
      pre =
        not
          (starA anyA;
           Put ((k [@d]), x_1, v, true);
           starA anyA);
      res = (not v : [%v: bool]);
      newadding = Exists ((k [@d]), v, not v);
    };
  |]

let[@libSRLRty] get ((a : int) [@ghost]) ?l:(k = (true : [%v: int])) =
  {
    pre =
      (starA anyA;
       Put ((k [@d]), (a [@d]), v, true);
       starA (anyA - Put ((k [@d]), x_1, v, true)));
    res = (v == a : [%v: int]);
    newadding = Get ((k [@d]), v, v == a);
  }
