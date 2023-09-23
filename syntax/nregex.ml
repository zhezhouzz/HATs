module T = struct
  include Minterm.T
  open Sexplib.Std

  type reg =
    | Empt
    | Epsilon
    | Any
    | Minterm of mt
    | Union of reg list
    | Intersect of reg list
    | Diff of reg * reg
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
      | Epsilon -> "ϵ"
      | Any -> "."
      | Minterm mt -> mt_to_string mt
      | Union rs -> spf "∪(%s)" @@ List.split_by_comma aux rs
      | Diff (t1, t2) -> spf "(%s \\ %s)" (aux t1) (aux t2)
      | Intersect rs -> spf "⊓(%s)" @@ List.split_by_comma aux rs
      | Concat rs -> List.split_by ";" aux rs
      | Star r -> spf "(%s)*" @@ aux r
      | Complement r -> spf "(%s)ᶜ" @@ aux r
    in
    aux reg

  let simp reg =
    let rec aux reg =
      match reg with
      | Epsilon | Empt | Any | Minterm _ -> reg
      | Diff (t1, t2) -> Diff (aux t1, aux t2)
      | Union rs -> (
          let rs = List.map aux rs in
          let rs =
            List.filter_map
              (fun x -> match x with Empt -> None | _ -> Some x)
              rs
          in
          match rs with [] -> Empt | [ x ] -> x | _ -> Union rs)
      | Intersect rs -> (
          let rs = List.map aux rs in
          if List.exists (fun x -> match x with Empt -> true | _ -> false) rs
          then Empt
          else match rs with [] -> Empt | [ x ] -> x | _ -> Intersect rs)
      | Concat rs -> (
          let rs = List.map aux rs in
          if List.exists (fun x -> match x with Empt -> true | _ -> false) rs
          then Empt
          else
            let rs =
              List.filter_map
                (fun x -> match x with Epsilon -> None | _ -> Some x)
                rs
            in
            match rs with [] -> Epsilon | [ x ] -> x | _ -> Concat rs)
      | Star r -> Star (aux r)
      | Complement r -> Complement (aux r)
    in
    aux reg
end
