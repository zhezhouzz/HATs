module T = struct
  include Minterm.T
  open Sexplib.Std

  type reg =
    | Epslion
    | Minterm of mt
    | Union of reg list
    | Intersect of reg list
    | Concat of reg list
    | Star of reg
  [@@deriving sexp]

  open Sugar
  open Zzdatatype.Datatype

  let reg_to_string reg =
    let rec aux reg =
      match reg with
      | Epslion -> "ε"
      | Minterm mt -> mt_to_string mt
      | Union rs -> spf "∪(%s)" @@ List.split_by_comma aux rs
      | Intersect rs -> spf "⊓(%s)" @@ List.split_by_comma aux rs
      | Concat rs -> List.split_by ";" aux rs
      | Star r -> spf "(%s)*" @@ aux r
    in
    aux reg
end
