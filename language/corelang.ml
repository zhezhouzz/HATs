module type T = sig
  type value [@@deriving sexp]
  type handler [@@deriving sexp]
  type comp [@@deriving sexp]
end

module F (Ty : Ty.T) : T = struct
  open Sexplib.Std

  type constant = Constant.t [@@deriving sexp]
  type 'a typed = { x : 'a; ty : Ty.t } [@@deriving sexp]

  type value =
    | VVar of string
    | VConst of constant
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VOpApp of { oparg : string typed }
    | VHd of handler typed

  and handler =
    | VHandler of {
        effi : value typed;
        retname : string typed;
        retc : comp typed;
        effarg : string typed;
        effk : string typed;
        effc : comp typed;
      }

  and comp =
    | CVal of value
    | CLet of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    | CApp of { appf : value typed; apparg : value typed }
    | CNewp
    | CWithH of { hd : handler typed; eprog : comp typed }
  [@@deriving sexp]
end
