open Sexplib.Std

type t = DtConstructor of string | External of string [@@deriving sexp]

let compare a b = Sexplib.Sexp.compare (sexp_of_t a) (sexp_of_t b)

let t_to_string_for_load = function
  | DtConstructor dt -> String.lowercase_ascii dt
  | External f -> f

let t_to_string = function
  | DtConstructor "Cons" -> "::"
  | DtConstructor "Nil" -> "[]"
  | DtConstructor dt -> dt
  | External f -> f

let from_source_name name =
  match name with
  | "[]" -> Some (DtConstructor "Nil")
  | "::" -> Some (DtConstructor "Cons")
  | _ ->
      if String.length name > 0 then
        let code = Char.code @@ String.get name 0 in
        if 65 <= code && code <= 90 then Some (DtConstructor name) else None
      else None
