module F (C: Corelang.T): T = struct
  open Sexplib.Std

  type constant = Constant.t [@@deriving sexp]

  type evalue =
    | EVConst of constant
    | EVEffi of int
    | EVLam of {evlamarg: string, evlambody: C.}
  and eres =
    | ERVal of evalue
    | EREffCall of {ereffi: int; erarg: value; era}
end
