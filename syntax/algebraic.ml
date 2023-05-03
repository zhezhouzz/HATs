module F (L : Lit.T) = struct
  type eqterm =
    | EqtRet of string L.typed
    | EqtDo of {
        dolhs : string L.typed;
        effop : string L.typed;
        effargs : string L.typed list;
        body : eqterm;
      }

  type equation = EqState of eqterm * eqterm | EqObv of eqterm * eqterm

  type t = {
    domain : Nt.t Zzdatatype.Datatype.StrMap.t;
    equationset : equation list;
  }

  open Sugar

  let layout _ = spf "%s::%i unimp" __FILE__ __LINE__

  type 'a typed = { x : 'a; ty : t }

  let layout_typed f { x; _ } = spf "%s:_" (f x)
end
