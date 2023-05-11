open Z3

(* open Z3aux *)
open Language.NRegex
open Sugar

let to_z3 ctx reg =
  let rec aux reg =
    match reg with
    | Epslion ->
        Seq.mk_re_empty ctx
          (Seq.mk_re_sort ctx (Seq.mk_seq_sort ctx (Seq.mk_string_sort ctx)))
    | Minterm { op; gobal_embedding; local_embedding } ->
        Seq.mk_seq_to_re ctx @@ Seq.mk_seq_unit ctx
        @@ Seq.mk_string ctx (spf "%s_%i_%i" op gobal_embedding local_embedding)
    | Union rs -> Seq.mk_re_union ctx @@ List.map aux rs
    | Concat rs -> Seq.mk_re_concat ctx @@ List.map aux rs
    | Star r -> Seq.mk_re_star ctx @@ aux r
  in
  aux reg
