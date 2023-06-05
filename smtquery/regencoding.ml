open Z3

(* open Z3aux *)
open Language.NRegex
open Sugar
open Zzdatatype.Datatype
open Z3reg
module RegZ3 = RegZ3BackendV0

let parse_reg encoding reg =
  let rec aux reg =
    match reg with
    | Epsilon | Any | Empt -> ()
    | Minterm mt -> RegZ3.insert_mt encoding mt
    | Union rs -> List.iter aux rs
    | Intersect rs -> List.iter aux rs
    | Concat rs -> List.iter aux rs
    | Star r -> aux r
    | Complement r -> aux r
  in
  aux reg

let get_size encoding reg =
  let rec aux reg =
    (* let () = Printf.printf "%s\n" @@ reg_to_string reg in *)
    match reg with
    | Any -> RegZ3.get_cardinal encoding
    | Empt | Epsilon | Minterm _ -> 1
    (* NOTE: z3 will raise exception when the length of the list < 2 *)
    | Union rs ->
        let bs = List.map aux rs in
        List.fold_left (fun sum n -> sum + n) 1 bs
    | Intersect rs ->
        let bs = List.map aux rs in
        List.fold_left (fun sum n -> sum + n) 1 bs
    | Concat rs ->
        let bs = List.map aux rs in
        List.fold_left (fun sum n -> sum + n) (List.length rs) bs
    | Star r -> 1 + aux r
    | Complement r ->
        let n = aux (Star Any) in
        1 + n + aux r
  in
  aux reg

let to_z3 ctx encoding reg =
  let rec aux reg =
    (* let () = Printf.printf "%s\n" @@ reg_to_string reg in *)
    match reg with
    | Any -> RegZ3.get_any ctx encoding
    | Empt -> mk_empty ctx
    | Epsilon -> mk_epsilon ctx
    | Minterm mt -> RegZ3.mt_to_z3 ctx encoding mt
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
    | Complement r ->
        let al = aux (Star Any) in
        Seq.mk_re_intersect ctx [ al; Seq.mk_re_complement ctx @@ aux r ]
  in
  aux reg

let to_z3_two_reg ctx (r1, r2) =
  let encoding = RegZ3.init () in
  let () = parse_reg encoding r1 in
  let () = parse_reg encoding r2 in
  (encoding, to_z3 ctx encoding r1, to_z3 ctx encoding r2)

let to_z3_one_reg ctx r =
  let encoding = RegZ3.init () in
  let () = parse_reg encoding r in
  (encoding, to_z3 ctx encoding r)
