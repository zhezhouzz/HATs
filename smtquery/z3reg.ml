let int_range_start = 48
let int_range_len = 10
let upper_range_start = 65
let upper_range_len = 26
let lower_range_start = 97
let lower_range_len = 26
let range_len = int_range_len + upper_range_len + lower_range_len

open Sugar
open Zzdatatype.Datatype
open Z3
open Language.NRegex

let mk_empty ctx =
  Seq.mk_re_empty ctx (Seq.mk_re_sort ctx (Seq.mk_string_sort ctx))

let mk_epsilon ctx = Seq.mk_re_option ctx @@ mk_empty ctx

(* NOTE: z3 will timeout over regular expression of language of (String String), e.g., ("AB" | "BC")("A")*. Thus we encoding the (String String) into String, i.g., (AB | BC)A*. To make the encoding to be efficient, distinguished string will be encodinged as distinguish char, e.g., (1 | 2)3*. *)

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
  let i = Char.code c in
  let res =
    if i < int_range_start + int_range_len then i - int_range_start
    else if i < upper_range_start + upper_range_len then
      i - upper_range_start + int_range_len
    else if i < lower_range_start + lower_range_len then
      i - lower_range_start + int_range_len + upper_range_len
    else _failatwith __FILE__ __LINE__ "die"
  in
  (* let () = Printf.printf "c:%c ==> %i ==> %i\n" c i res in *)
  res

module RegZ3BackendV0 = struct
  type encoding = { tab : (string, int) Hashtbl.t; next : int ref }

  let get_cardinal { tab; _ } = Hashtbl.length tab
  let init () = { tab = Hashtbl.create range_len; next = ref 0 }

  let next_next n =
    let n' = n + 1 in
    if n' > range_len then _failatwith __FILE__ __LINE__ "RegZ3BackendV0"
    else n'

  let print_encoding { tab; _ } =
    Hashtbl.iter
      (fun mt id -> Printf.printf "%s => %i => %c\n" mt id (int_to_char id))
      tab

  let insert_mt { tab; next } mt =
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

  let i_to_z3 ctx n =
    Seq.mk_seq_to_re ctx @@ Seq.mk_string ctx
    @@ String.init 1 (fun _ -> int_to_char n)

  let mt_to_z3 ctx { tab; _ } mt =
    let n = Hashtbl.find tab (mt_to_string mt) in
    i_to_z3 ctx n

  let mt_to_string { tab; _ } mt =
    let n = Hashtbl.find tab (mt_to_string mt) in
    String.init 1 (fun _ -> int_to_char n)

  let get_any ctx { tab; _ } =
    (* let l = List.of_seq (Hashtbl.to_seq_values tab) in *)
    (* let () = *)
    (*   Printf.printf "Z#:%s\n" *)
    (*     (List.split_by_comma *)
    (*        (fun x -> spf "%s" @@ Expr.to_string (il_to_z3 ctx x)) *)
    (*        l) *)
    (* in *)
    let res =
      List.map (i_to_z3 ctx) @@ List.of_seq (Hashtbl.to_seq_values tab)
    in
    let res =
      match res with
      | [] -> mk_empty ctx
      | [ r ] -> r
      | _ -> Seq.mk_re_union ctx res
    in
    (* let () = Printf.printf "Z#: %s\n" (Expr.to_string res) in *)
    res

  let rev_find_opt tab il =
    Hashtbl.fold
      (fun k v res ->
        (* let () = Printf.printf "k: %s -> v: %s\n" k (IntList.to_string v) in *)
        match res with
        | Some res -> Some res
        | None -> if il == v then Some k else None)
      tab None

  let code_trace { tab; _ } str =
    let cs_list = List.of_seq @@ String.to_seq str in
    let il_list = List.map char_to_int cs_list in
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
end

module RegZ3BackendV2 = struct
  open Z3hex

  type encoding = { tab : (string, int) Hashtbl.t; next : int ref }

  let get_cardinal { tab; _ } = Hashtbl.length tab
  let init () = { tab = Hashtbl.create range_len; next = ref 0 }

  let next_next n =
    let n' = n + 1 in
    if n' > hex_range then
      _failatwith __FILE__ __LINE__
      @@ spf "RegZ3BackendV2 (%i > %i)" n' hex_range
    else n'

  let print_encoding { tab; _ } =
    Hashtbl.iter
      (fun mt id -> Printf.printf "%s => %i => %s\n" mt id (int_to_hexstr id))
      tab

  let insert_mt { tab; next } mt =
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

  let i_to_z3 ctx n =
    Seq.mk_seq_to_re ctx @@ Seq.mk_string ctx (int_to_hexstr n)

  let mt_to_z3 ctx { tab; _ } mt =
    let n = Hashtbl.find tab (mt_to_string mt) in
    i_to_z3 ctx n

  let mt_to_string { tab; _ } mt =
    let n = Hashtbl.find tab (mt_to_string mt) in
    int_to_hexstr n

  let get_any ctx { tab; _ } =
    (* let l = List.of_seq (Hashtbl.to_seq_values tab) in *)
    (* let () = *)
    (*   Printf.printf "Z#:%s\n" *)
    (*     (List.split_by_comma *)
    (*        (fun x -> spf "%s" @@ Expr.to_string (il_to_z3 ctx x)) *)
    (*        l) *)
    (* in *)
    let res =
      List.map (i_to_z3 ctx) @@ List.of_seq (Hashtbl.to_seq_values tab)
    in
    let res =
      match res with
      | [] -> mk_empty ctx
      | [ r ] -> r
      | _ -> Seq.mk_re_union ctx res
    in
    (* let () = Printf.printf "Z#: %s\n" (Expr.to_string res) in *)
    res

  let rev_find_opt tab il =
    Hashtbl.fold
      (fun k v res ->
        (* let () = Printf.printf "k: %s -> v: %s\n" k (IntList.to_string v) in *)
        match res with
        | Some res -> Some res
        | None -> if il == v then Some k else None)
      tab None

  let code_trace { tab; _ } str =
    let il_list = intlist_of_hexstrs str in
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
end

module RegZ3BackendV1 = struct
  let delimit = '_'

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

  let rec next_next l =
    match l with
    | [] -> [ 0 ]
    | hd :: tl ->
        let hd' = hd + 1 in
        if hd' < range_len then hd' :: tl else 0 :: next_next tl

  type encoding = { tab : (string, int list) Hashtbl.t; next : int list ref }

  let get_cardinal { tab; _ } = Hashtbl.length tab
  let init () = { tab = Hashtbl.create range_len; next = ref [ 0 ] }

  let insert_mt { tab; next } mt =
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

  let mt_to_z3 ctx { tab; _ } mt =
    il_to_z3 ctx @@ Hashtbl.find tab (mt_to_string mt)

  let get_any ctx { tab; _ } =
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

  let rev_find_opt tab il =
    Hashtbl.fold
      (fun k v res ->
        (* let () = Printf.printf "k: %s -> v: %s\n" k (IntList.to_string v) in *)
        match res with
        | Some res -> Some res
        | None -> if List.equal ( == ) il v then Some k else None)
      tab None

  let code_trace { tab; _ } str =
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
end
