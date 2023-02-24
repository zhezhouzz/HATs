module type T = functor (Ty : Ty.T) -> sig
  type constant = Constant.t [@@deriving sexp]
  type ty = Ty.t [@@deriving sexp]
  type 'a typed = { x : 'a; ty : Ty.t } [@@deriving sexp]

  type value =
    | VVar of string
    | VConst of constant
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VOp of string
    | VHd of handler typed

  and handler_case = {
    effop : string typed;
    effargs : string typed list;
    effk : string typed;
    hbody : comp typed;
  }

  and ret_case = { retarg : string typed; retbody : comp typed }
  and handler = { ret_case : ret_case; handler_cases : handler_case list }

  and comp =
    | CVal of value
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    | CLetApp of {
        lhs : string typed;
        rhsf : value typed;
        rhsarg : value typed;
        letbody : comp typed;
      }
    | CLetPerform of {
        lhs : string typed;
        rhsop : string typed;
        rhsargs : value typed list;
        letbody : comp typed;
      }
    | CWithH of { handler : handler typed; handled_prog : comp typed }
  [@@deriving sexp]
end

module F : T =
functor
  (Ty : Ty.T)
  ->
  struct
    open Sexplib.Std

    type constant = Constant.t [@@deriving sexp]
    type ty = Ty.t [@@deriving sexp]
    type 'a typed = { x : 'a; ty : ty } [@@deriving sexp]

    type value =
      | VVar of string
      | VConst of constant
      | VLam of { lamarg : string typed; lambody : comp typed }
      | VOp of string
      | VHd of handler typed

    and handler_case = {
      effop : string typed;
      effargs : string typed list;
      effk : string typed;
      hbody : comp typed;
    }

    and ret_case = { retarg : string typed; retbody : comp typed }
    and handler = { ret_case : ret_case; handler_cases : handler_case list }

    and comp =
      | CVal of value
      | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
      | CLetApp of {
          lhs : string typed;
          rhsf : value typed;
          rhsarg : value typed;
          letbody : comp typed;
        }
      | CLetPerform of {
          lhs : string typed;
          rhsop : string typed;
          rhsargs : value typed list;
          letbody : comp typed;
        }
      | CWithH of { handler : handler typed; handled_prog : comp typed }
    [@@deriving sexp]
  end
