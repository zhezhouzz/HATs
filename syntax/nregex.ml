module T = struct
  include Minterm.T
  open Sexplib.Std

  type reg =
    | Empt
    | Epslion
    | Minterm of mt
    | Union of reg list
    | Intersect of reg list
    | Concat of reg list
    | Star of reg
    | Complement of reg
  [@@deriving sexp]

  open Sugar
  open Zzdatatype.Datatype

  let reg_to_string reg =
    let rec aux reg =
      match reg with
      | Empt -> "∅"
      | Epslion -> "ε"
      | Minterm mt -> mt_to_string mt
      | Union rs -> spf "∪(%s)" @@ List.split_by_comma aux rs
      | Intersect rs -> spf "⊓(%s)" @@ List.split_by_comma aux rs
      | Concat rs -> List.split_by ";" aux rs
      | Star r -> spf "(%s)*" @@ aux r
      | Complement r -> spf "(%s)ᶜ" @@ aux r
    in
    aux reg

  (* let simp reg = *)
  (*   let rec aux reg = *)
  (*     match reg with *)
  (*     | Epslion | Minterm _ -> reg *)
  (*     | Union rs -> ( *)
  (*         let rs = List.map aux rs in *)
  (*         let rs = *)
  (*           List.filter_map *)
  (*             (fun x -> match x with Epslion -> None | _ -> Some x) *)
  (*             rs *)
  (*         in *)
  (*         match rs with [] -> Epslion | [ x ] -> x | _ -> Union rs) *)
  (*     | Intersect rs -> ( *)
  (*         let rs = List.map aux rs in *)
  (*         if *)
  (*           List.exists *)
  (*             (fun x -> match x with Epslion -> true | _ -> false) *)
  (*             rs *)
  (*         then Epslion *)
  (*         else *)
  (*           match rs with [] -> Intersect [] | [ x ] -> x | _ -> Intersect rs) *)
  (*     | Concat rs ->  *)

  (*       ( *)
  (*         let rs = List.map aux rs in *)
  (*         let rs = *)
  (*           List.filter_map *)
  (*             (fun x -> match x with Epslion -> None | _ -> Some x) *)
  (*             rs *)
  (*         in *)
  (*         match rs with [] -> Epslion | [ x ] -> x | _ -> Concat rs) *)
  (*     | Star r -> Star (aux r) *)
  (*   in *)
  (*   aux reg *)
end
