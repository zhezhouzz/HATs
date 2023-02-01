module type T = sig
  type repr [@@deriving sexp]
  type res [@@deriving sexp]
  type effi = int [@@deriving sexp]
end

module T : T = struct
  open Sexplib.Std

  type repr = BI of int | BU | F of { farg : string; fbody : res }
  [@@deriving sexp]

  and res =
    | V of repr
    | E of { inst : int; arg : repr; karg : string; kbody : res }
  [@@deriving sexp]

  type effi = int [@@deriving sexp]
  (* type effhd = { harg : string; hbody : res } [@@deriving sexp] *)
end
