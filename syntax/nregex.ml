module T = struct
  open Sexplib.Std

  type reg =
    | Epslion
    | Minterm of string * int
    | Union of reg list
    | Concat of reg list
    | Star of reg
  [@@deriving sexp]
end
