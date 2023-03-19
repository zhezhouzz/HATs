module type T = sig
  type constant = Constant.t [@@deriving sexp]

  include Typed.T

  type term =
    | Var of string
    | Const of constant
    | Lam of { lamarg : string typed; lambody : term typed }
    | VHd of handler typed
    (* term *)
    | Err
    | Let of {
        if_rec : bool;
        lhs : string typed;
        rhs : term typed;
        letbody : term typed;
      }
    | App of term typed * term typed
    | AppOp of string typed * term typed list
    | Perform of { rhsop : string typed; rhsargs : term typed list }
    | CWithH of { handler : handler typed; handled_prog : term typed }
    | Ite of term typed * term typed * term typed
    | Tu of term typed list

  and handler_case = {
    effop : string typed;
    effargs : string typed list;
    effk : string typed;
    hbody : term typed;
  }

  and ret_case = { retarg : string typed; retbody : term typed }

  and handler = { ret_case : ret_case; handler_cases : handler_case list }
  [@@deriving sexp]

  val mk_var : string -> term typed
  val mk_bool : bool -> term typed
  val mk_int : int -> term typed
end

module F (Ty : Typed.T) : T with type t = Ty.t = struct
  open Sexplib.Std

  type constant = Constant.t [@@deriving sexp]

  include Ty

  type term =
    | Var of string
    | Const of constant
    | Lam of { lamarg : string typed; lambody : term typed }
    | VHd of handler typed
    (* term *)
    | Err
    | Let of {
        if_rec : bool;
        lhs : string typed;
        rhs : term typed;
        letbody : term typed;
      }
    | App of term typed * term typed
    | AppOp of string typed * term typed list
    | Perform of { rhsop : string typed; rhsargs : term typed list }
    | CWithH of { handler : handler typed; handled_prog : term typed }
    | Ite of term typed * term typed * term typed
    | Tu of term typed list

  and handler_case = {
    effop : string typed;
    effargs : string typed list;
    effk : string typed;
    hbody : term typed;
  }

  and ret_case = { retarg : string typed; retbody : term typed }

  and handler = { ret_case : ret_case; handler_cases : handler_case list }
  [@@deriving sexp]

  let mk_var name = mk_noty @@ Var name
  let mk_bool b = (Const (Constant.B b)) #: bool_ty
  let mk_int i = (Const (Constant.I i)) #: int_ty
end
