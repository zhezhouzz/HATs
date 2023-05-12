open Z3

(* open Z3aux *)
open Language.NRegex
open Sugar
open Zzdatatype.Datatype

(* let mk_empty ctx = *)
(*   Seq.mk_re_empty ctx *)
(*     (Seq.mk_re_sort ctx (Seq.mk_seq_sort ctx (Seq.mk_string_sort ctx))) *)

(* let mk_full ctx = *)
(*   Seq.mk_re_full ctx *)
(*     (Seq.mk_re_sort ctx (Seq.mk_seq_sort ctx (Seq.mk_string_sort ctx))) *)

let mk_empty ctx =
  Seq.mk_re_empty ctx (Seq.mk_re_sort ctx (Seq.mk_string_sort ctx))

let mk_full ctx =
  Seq.mk_re_full ctx (Seq.mk_re_sort ctx (Seq.mk_string_sort ctx))

let int_range_start = 48
let int_range_len = 10
let upper_range_start = 65
let upper_range_len = 26
let lower_range_start = 65
let lower_range_len = 26
let range_len = int_range_len + upper_range_len + lower_range_len
let delimit = '_'

let int_to_char i =
  if i < int_range_len then Char.chr (i + int_range_start)
  else if i < int_range_len + upper_range_len then
    Char.chr (i + upper_range_start)
  else if i < int_range_len + upper_range_len + lower_range_len then
    Char.chr (i + lower_range_start)
  else _failatwith __FILE__ __LINE__ "die"

let il_to_chars il =
  String.of_seq @@ List.to_seq @@ (delimit :: List.map int_to_char il)

let il_to_z3 ctx il =
  Seq.mk_seq_to_re ctx @@ Seq.mk_string ctx @@ il_to_chars il

type encoding = { tab : (string, int list) Hashtbl.t; next : int list ref }

let rec next_next l =
  match l with
  | [] -> [ 0 ]
  | hd :: tl ->
      let hd' = hd + 1 in
      if hd' < range_len then hd' :: tl else 0 :: next_next l

let encoding_insert_mt { tab; next } mt =
  let str = mt_to_string mt in
  match Hashtbl.find_opt tab str with
  | None ->
      Hashtbl.add tab str !next;
      let next' = next_next !next in
      (* let () = *)
      (*   Printf.printf "next: %s\n" @@ List.split_by_comma string_of_int next' *)
      (* in *)
      next := next' (* { tab; next = next_next next } *)
  | Some _ -> ()

let encoding_mt_to_z3 ctx { tab; _ } mt =
  il_to_z3 ctx @@ Hashtbl.find tab (mt_to_string mt)

let encoding_init () = { tab = Hashtbl.create range_len; next = ref [ 0 ] }

let encoding_parse_reg encoding reg =
  let rec aux reg =
    match reg with
    | Epslion -> ()
    | Minterm mt -> encoding_insert_mt encoding mt
    | Union rs -> List.iter aux rs
    | Intersect rs -> List.iter aux rs
    | Concat rs -> List.iter aux rs
    | Star r -> aux r
  in
  aux reg

let to_z3 ctx encoding reg =
  let rec aux reg =
    (* let () = Printf.printf "%s\n" @@ reg_to_string reg in *)
    match reg with
    | Epslion -> mk_empty ctx
    | Minterm mt -> encoding_mt_to_z3 ctx encoding mt
    (* let z3_str = Seq.mk_string ctx @@ mt_to_string mt in *)
    (* let () = Printf.printf "z3_str: %s\n" @@ Expr.to_string z3_str in *)
    (* let res = Seq.mk_seq_to_re ctx @@ Seq.mk_seq_unit ctx z3_str in *)
    (* let () = Printf.printf "%s??\n" @@ reg_to_string reg in *)
    (* res *)
    (* NOTE: z3 will raise exception when the length of the list < 2 *)
    | Union [] -> mk_empty ctx
    | Union [ r ] -> aux r
    | Union rs ->
        (* let () = Printf.printf "len(union rs) = %i\n" @@ List.length rs in *)
        Seq.mk_re_union ctx @@ List.map aux rs
    | Intersect [] -> mk_full ctx
    | Intersect [ r ] -> aux r
    | Intersect rs ->
        (* let () = Printf.printf "len(intersect rs) = %i\n" @@ List.length rs in *)
        Seq.mk_re_intersect ctx @@ List.map aux rs
    | Concat [] -> _failatwith __FILE__ __LINE__ "die"
    | Concat [ r ] -> aux r
    | Concat rs ->
        (* let () = Printf.printf "len(concat rs) = %i\n" @@ List.length rs in *)
        let rs' = List.map aux rs in
        (* let () = *)
        (*   Printf.printf "%s\n" @@ List.split_by " ? " Expr.to_string rs' *)
        (* in *)
        Seq.mk_re_concat ctx rs'
    | Star r -> Seq.mk_re_star ctx @@ aux r
  in
  aux reg

let to_z3_two_reg ctx (r1, r2) =
  let encoding = encoding_init () in
  encoding_parse_reg encoding r1;
  encoding_parse_reg encoding r2;
  (to_z3 ctx encoding r1, to_z3 ctx encoding r2)
