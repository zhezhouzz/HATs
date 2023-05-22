open Z3

(* open Z3aux *)
open Language.NRegex
open Sugar
open Zzdatatype.Datatype

let mk_empty ctx =
  Seq.mk_re_empty ctx (Seq.mk_re_sort ctx (Seq.mk_string_sort ctx))

let mk_epsilon ctx = Seq.mk_re_option ctx @@ mk_empty ctx

(* let mk_full ctx = *)
(*   Seq.mk_re_full ctx (Seq.mk_re_sort ctx (Seq.mk_string_sort ctx)) *)

(* NOTE: z3 will timeout over regular expression of language of (String String), e.g., ("AB" | "BC")("A")*. Thus we encoding the (String String) into String, i.g., (AB | BC)A*. To make the encoding to be efficient, distinguished string will be encodinged as distinguish char, e.g., (1 | 2)3*. *)

let int_range_start = 48
let int_range_len = 10
let upper_range_start = 65
let upper_range_len = 26
let lower_range_start = 97
let lower_range_len = 26
let range_len = int_range_len + upper_range_len + lower_range_len
let delimit = '_'

let int_to_char i =
  if i < int_range_len then Char.chr (i + int_range_start)
  else
    let i = i - int_range_len in
    if i < upper_range_len then Char.chr (i + upper_range_start)
    else
      let i = i - upper_range_len in
      if i < lower_range_len then Char.chr (i + lower_range_start)
      else _failatwith __FILE__ __LINE__ "die"

let char_to_int c =
  (* let () = Printf.printf "c:%c\n" c in *)
  let i = Char.code c in
  let i' = i - int_range_start in
  if i' < int_range_len then i'
  else
    let i' = i - upper_range_start in
    if i' < upper_range_len then i'
    else
      let i' = i - lower_range_start in
      if i' < lower_range_len then i' else _failatwith __FILE__ __LINE__ "die"

let il_to_chars il =
  String.of_seq @@ List.to_seq @@ (delimit :: List.map int_to_char il)

let chars_to_il str =
  let cs = List.of_seq @@ String.to_seq str in
  List.map char_to_int cs
(* match cs with *)
(* | di :: cs when Char.equal di delimit -> List.map char_to_int cs *)
(* | _ -> _failatwith __FILE__ __LINE__ "?" *)

let il_to_z3 ctx il =
  Seq.mk_seq_to_re ctx @@ Seq.mk_string ctx @@ il_to_chars il

type encoding = { tab : (string, int list) Hashtbl.t; next : int list ref }

let rec next_next l =
  match l with
  | [] -> [ 0 ]
  | hd :: tl ->
      let hd' = hd + 1 in
      if hd' < range_len then hd' :: tl else 0 :: next_next tl

let encoding_insert_mt { tab; next } mt =
  (* let () = Pp.printf "@{<orange>next:@} %s\n" (il_to_chars !next) in *)
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

let encoding_get_any ctx { tab; _ } =
  (* let l = List.of_seq (Hashtbl.to_seq_values tab) in *)
  (* let () = *)
  (*   Printf.printf "Z#:%s\n" *)
  (*     (List.split_by_comma *)
  (*        (fun x -> spf "%s" @@ Expr.to_string (il_to_z3 ctx x)) *)
  (*        l) *)
  (* in *)
  let res =
    List.map (il_to_z3 ctx) @@ List.of_seq (Hashtbl.to_seq_values tab)
  in
  let res =
    match res with
    | [] -> mk_empty ctx
    | [ r ] -> r
    | _ -> Seq.mk_re_union ctx res
  in
  (* let () = Printf.printf "Z#: %s\n" (Expr.to_string res) in *)
  res

let encoding_parse_reg encoding reg =
  let rec aux reg =
    match reg with
    | Epsilon | Any | Empt -> ()
    | Minterm mt -> encoding_insert_mt encoding mt
    | Union rs -> List.iter aux rs
    | Intersect rs -> List.iter aux rs
    | Concat rs -> List.iter aux rs
    | Star r -> aux r
    | Complement r -> aux r
  in
  aux reg

let rev_find_opt tab il =
  Hashtbl.fold
    (fun k v res ->
      (* let () = Printf.printf "k: %s -> v: %s\n" k (IntList.to_string v) in *)
      match res with
      | Some res -> Some res
      | None -> if List.equal ( == ) il v then Some k else None)
    tab None

let encoding_code_trace { tab; _ } str =
  (* let () = Printf.printf "str:%s\n" str in *)
  let cs_list =
    List.filter
      (fun l -> String.length l > 0)
      (String.split_on_char delimit str)
  in
  (* let () = *)
  (*   Printf.printf "?len(il): %i\n" (String.length (List.nth cs_list 0)) *)
  (* in *)
  (* let cs_list = List.map (fun str -> "_" ^ str) cs_list in *)
  let il_list = List.map chars_to_il cs_list in
  (* let () = Printf.printf "?len(il): %i\n" (List.length (List.nth il_list 0)) in *)
  let mt_list =
    List.map
      (fun il ->
        (* let () = *)
        (*   Printf.printf "il: %s\n" (List.split_by_comma string_of_int il) *)
        (* in *)
        match rev_find_opt tab il with
        | Some mt_str ->
            (* let () = Printf.printf "mt_str: %s\n" mt_str in *)
            string_to_mt mt_str
        | None -> _failatwith __FILE__ __LINE__ "die")
      il_list
  in
  mt_list

let to_z3 ctx encoding reg =
  let rec aux reg =
    (* let () = Printf.printf "%s\n" @@ reg_to_string reg in *)
    match reg with
    | Any -> encoding_get_any ctx encoding
    | Empt -> mk_empty ctx
    | Epsilon -> mk_epsilon ctx
    | Minterm mt -> encoding_mt_to_z3 ctx encoding mt
    (* NOTE: z3 will raise exception when the length of the list < 2 *)
    | Union [] -> mk_empty ctx
    | Union [ r ] -> aux r
    | Union rs ->
        (* let () = Printf.printf "len(union rs) = %i\n" @@ List.length rs in *)
        Seq.mk_re_union ctx @@ List.map aux rs
    | Intersect [] -> _failatwith __FILE__ __LINE__ "die"
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
    (* | Star (Complement Empt) -> mk_full ctx *)
    | Star r -> Seq.mk_re_star ctx @@ aux r
    (* | Complement Empt -> mk_full ctx *)
    | Complement r -> Seq.mk_re_complement ctx @@ aux r
  in
  aux reg

let to_z3_two_reg ctx (r1, r2) =
  let encoding = encoding_init () in
  let () = encoding_parse_reg encoding r1 in
  let () = encoding_parse_reg encoding r2 in
  (encoding, to_z3 ctx encoding r1, to_z3 ctx encoding r2)

let to_z3_one_reg ctx r =
  let encoding = encoding_init () in
  let () = encoding_parse_reg encoding r in
  (encoding, to_z3 ctx encoding r)
