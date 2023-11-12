module F (L : Lit.T) = struct
  open Sexplib.Std
  module SE = Sevent.F (L)
  include SE

  type regex =
    | EmptyA
    | EpsilonA
    | AnyA
    | EventA of sevent
    | LorA of regex * regex
    | LandA of regex * regex
    | SeqA of regex * regex
    | StarA of regex
    | ComplementA of regex
    | SetMinusA of regex * regex
  [@@deriving sexp]

  type sfa = regex [@@deriving sexp]

  let raw_to_string r = Sexplib.Sexp.to_string @@ sexp_of_regex r

  (* open Sugar *)
  (* open Common *)

  let mk_regex_any = AnyA
  let mk_regex_all = StarA AnyA

  let smart_seq (a1, a2) =
    match a1 with EmptyA -> EmptyA | EpsilonA -> a2 | _ -> SeqA (a1, a2)

  (* open Sugar *)

  let compare l1 l2 = Sexplib.Sexp.compare (sexp_of_regex l1) (sexp_of_regex l2)
  let eq l1 l2 = 0 == compare l1 l2

  let rec is_empty a =
    match a with
    | EmptyA -> true
    | EpsilonA | AnyA | EventA _ -> false
    | LorA (a1, a2) -> is_empty a1 && is_empty a2
    | LandA (a1, a2) -> is_empty a1 || is_empty a2
    | SeqA (a1, a2) -> is_empty a1 || is_empty a2
    | StarA a -> is_empty a
    | ComplementA _ -> false
    | SetMinusA (a1, a2) -> eq a1 a2

  type sfa_len = EmptySet | HasUniqLen of int | MayNoUniqLen [@@deriving sexp]

  let compare_sfa_len l1 l2 =
    Sexplib.Sexp.compare (sexp_of_sfa_len l1) (sexp_of_sfa_len l2)

  let eq_sfa_len l1 l2 = 0 == compare_sfa_len l1 l2

  (* if the traces accpected by th SFA as the same length, return it; otherwise none. *)
  let rec has_len_aux a =
    match a with
    | EmptyA -> EmptySet
    | EpsilonA -> HasUniqLen 0
    | AnyA | EventA _ -> HasUniqLen 1
    | LorA (a1, a2) -> (
        match (has_len_aux a1, has_len_aux a2) with
        | EmptySet, l2 -> l2
        | l1, EmptySet -> l1
        | HasUniqLen n1, HasUniqLen n2 when n1 == n2 -> HasUniqLen n1
        | _ -> MayNoUniqLen)
    | LandA (a1, a2) -> (
        match (has_len_aux a1, has_len_aux a2) with
        | EmptySet, _ | _, EmptySet -> EmptySet
        | HasUniqLen n1, HasUniqLen n2 when n1 == n2 -> HasUniqLen n1
        | _ -> MayNoUniqLen)
    | SeqA (a1, a2) -> (
        match (has_len_aux a1, has_len_aux a2) with
        | EmptySet, _ | _, EmptySet -> EmptySet
        | HasUniqLen n1, HasUniqLen n2 -> HasUniqLen (n1 + n2)
        | _ -> MayNoUniqLen)
    | StarA a -> (
        match has_len_aux a with
        | EmptySet -> EmptySet
        | HasUniqLen 0 -> HasUniqLen 0
        | _ -> MayNoUniqLen)
    | ComplementA _ -> MayNoUniqLen
    | SetMinusA (a1, a2) -> (
        match (has_len_aux a1, has_len_aux a2) with
        | EmptySet, _ -> EmptySet
        | l1, EmptySet -> l1
        | HasUniqLen n1, HasUniqLen n2 when n1 == n2 -> HasUniqLen n1
        | _ -> MayNoUniqLen)

  (* let is_empty a = match has_len_aux a with EmptySet -> true | _ -> false *)

  let has_len a n =
    match has_len_aux a with HasUniqLen m -> n == m | _ -> false

  let rec be_singleton a =
    match a with
    | EmptyA -> EmptyA
    | EpsilonA -> EmptyA
    | AnyA -> AnyA
    | EventA _ -> a
    | LorA (a1, a2) -> LorA (be_singleton a1, be_singleton a2)
    | LandA (a1, a2) -> LandA (be_singleton a1, be_singleton a2)
    | SeqA (a1, a2) -> (
        match has_len_aux a1 with
        | EmptySet -> EmptyA
        | HasUniqLen 0 -> be_singleton a2
        | HasUniqLen 1 -> a1
        | _ -> LandA (AnyA, a))
    | StarA a -> be_singleton a
    | ComplementA _ -> LandA (AnyA, a)
    | SetMinusA (a1, a2) -> SetMinusA (be_singleton a1, be_singleton a2)

  open Sugar

  let is_aligned (r1, r2) =
    match (has_len_aux r1, has_len_aux r2) with
    | EmptySet, EmptySet -> true
    | HasUniqLen n, HasUniqLen n' when n == n' -> true
    | _, _ -> false
  (* eq_sfa_len (has_len_aux r1) (has_len_aux r2) *)

  type layout_setting = {
    sym_true : string;
    sym_false : string;
    sym_and : string;
    sym_or : string;
    sym_not : string;
    sym_implies : string;
    sym_iff : string;
    sym_forall : string;
    sym_exists : string;
    layout_typedid : string Nt.typed -> string;
    layout_mp : string -> string;
  }

  let psetting =
    {
      sym_true = "⊤";
      sym_false = "⊥";
      sym_and = " ∧ ";
      sym_or = " ∨ ";
      sym_not = "¬";
      sym_implies = "=>";
      sym_iff = "<=>";
      sym_forall = "∀";
      sym_exists = "∃";
      layout_typedid = (fun x -> x.x);
      (* (fun x ->          Printf.spf "(%s:%s)" x.x (Ty.layout x.ty)); *)
      layout_mp = (fun x -> x);
    }

  let rec raw_pprint_aux = function
    | EmptyA -> ("∅", true)
    | EpsilonA -> ("ϵ", true)
    | EventA _ -> ("se", true)
    | LorA (a1, a2) ->
        (spf "%s%s%s" (raw_p_pprint a1) psetting.sym_or (raw_p_pprint a2), false)
    | SetMinusA (a1, a2) ->
        (spf "%s\\%s" (raw_p_pprint a1) (raw_p_pprint a2), false)
    | LandA (a1, a2) ->
        ( spf "%s%s%s" (raw_p_pprint a1) psetting.sym_and (raw_p_pprint a2),
          false )
    | SeqA (a1, a2) -> (spf "%s;%s" (raw_p_pprint a1) (raw_p_pprint a2), false)
    (* | StarA AnyA -> (".*", true) *)
    | StarA a -> (spf "%s*" (raw_p_pprint a), true)
    | AnyA -> (".", true)
    (* | ComplementA (EventA se) -> spf "%sᶜ" (pprint (EventA se)) *)
    | ComplementA a -> (spf "%sᶜ" (raw_p_pprint a), true)

  (* let rec raw_pprint_aux = function *)
  (*   | EmptyA -> ("∅", true) *)
  (*   | EpsilonA -> ("ϵ", true) *)
  (*   | EventA se -> (To_se.pprint se, true) *)
  (*   | LorA (a1, a2) -> *)
  (*       (spf "%s%s%s" (raw_p_pprint a1) psetting.sym_or (raw_p_pprint a2), false) *)
  (*   | SetMinusA (a1, a2) -> (spf "%s\\%s" (raw_p_pprint a1) (raw_p_pprint a2), false) *)
  (*   | LandA (a1, a2) -> *)
  (*       (spf "%s%s%s" (raw_p_pprint a1) psetting.sym_and (raw_p_pprint a2), false) *)
  (*   | SeqA (a1, a2) -> (spf "%s;%s" (raw_p_pprint a1) (raw_p_pprint a2), false) *)
  (*   (\* | StarA AnyA -> (".*", true) *\) *)
  (*   | StarA a -> (spf "%s*" (raw_p_pprint a), true) *)
  (*   | AnyA -> (".", true) *)
  (*   (\* | ComplementA (EventA se) -> spf "%sᶜ" (pprint (EventA se)) *\) *)
  (*   | ComplementA a -> (spf "%sᶜ" (raw_p_pprint a), true) *)

  and raw_p_pprint a =
    let str, is_p = raw_pprint_aux a in
    if is_p then str else spf "(%s)" str

  let rec simpl r =
    let res =
      match r with
      | EventA (GuardEvent phi) when is_true phi -> AnyA
      | EventA (GuardEvent phi) when is_false phi -> EmptyA
      | EmptyA | EpsilonA | AnyA | EventA _ -> r
      | LorA (r1, r2) -> (
          let r1, r2 = map2 simpl (r1, r2) in
          match (r1, r2) with
          | StarA AnyA, _ | _, StarA AnyA -> StarA AnyA
          | SeqA (r11, r12), SeqA (r21, r22) when is_aligned (r11, r21) ->
              SeqA (simpl (LorA (r11, r21)), simpl (LorA (r12, r22)))
          | _, _ -> (
              match (has_len_aux r1, has_len_aux r2) with
              | EmptySet, _ -> r2
              | _, EmptySet -> r1
              | _ -> LorA (r1, r2)))
      | LandA (r1, r2) -> (
          let r1, r2 = map2 simpl (r1, r2) in
          match (r1, r2) with
          | StarA AnyA, r2 -> r2
          | r1, StarA AnyA -> r1
          | SeqA (r11, r12), SeqA (r21, r22) when is_aligned (r11, r21) ->
              SeqA (simpl (LandA (r11, r21)), simpl (LandA (r12, r22)))
          | _, _ -> (
              match (has_len_aux r1, has_len_aux r2) with
              | EmptySet, _ | _, EmptySet -> EmptyA
              | _ -> (
                  match (r1, r2) with
                  | AnyA, _ -> be_singleton r2
                  | _, AnyA -> be_singleton r1
                  | _, _ -> LandA (r1, r2))))
      | SeqA (r1, r2) -> (
          let r1, r2 = map2 simpl (r1, r2) in
          match (has_len_aux r1, has_len_aux r2) with
          | EmptySet, _ | _, EmptySet -> EmptyA
          | HasUniqLen 0, _ -> r2
          | _, HasUniqLen 0 -> r1
          | _ -> SeqA (r1, r2))
      | StarA r -> (
          let r = simpl r in
          match has_len_aux r with
          | EmptySet -> EmptyA
          | HasUniqLen 0 -> EpsilonA
          | _ -> StarA r)
      | ComplementA (ComplementA a) -> simpl a
      | ComplementA a -> (
          let a' = simpl a in
          match a' with ComplementA a' -> a' | _ -> ComplementA a')
      | SetMinusA (r1, r2) -> (
          let r1, r2 = map2 simpl (r1, r2) in
          match (has_len_aux r1, has_len_aux r2) with
          | EmptySet, _ -> EmptyA
          | _, EmptySet -> r1
          | _ -> SetMinusA (r1, r2))
    in
    (* let () = *)
    (*   Env.show_log "desymbolic" @@ fun _ -> *)
    (*   if not (eq r res) then ( *)
    (*     Pp.printf "@{<bold>[--simpl] regex before:@} %s\n" (raw_p_pprint r); *)
    (*     Pp.printf "@{<bold>[--simpl] regex after:@} %s\n" (raw_p_pprint res)) *)
    (* in *)
    res

  (* subst *)

  let subst (y, z) regex =
    let rec aux regex =
      match regex with
      | EmptyA -> EmptyA
      | AnyA -> AnyA
      | EpsilonA -> EpsilonA
      | EventA se -> EventA (SE.subst (y, z) se)
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SetMinusA (t1, t2) -> SetMinusA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
      | ComplementA t -> ComplementA (aux t)
    in
    aux regex

  let subst_id (y, z) rty =
    let z = AVar z in
    subst (y, z) rty

  (* fv *)

  let fv regex =
    let rec aux regex =
      match regex with
      | EmptyA -> []
      | AnyA -> []
      | EpsilonA -> []
      | EventA se -> SE.fv se
      | LorA (t1, t2) -> aux t1 @ aux t2
      | SetMinusA (t1, t2) -> aux t1 @ aux t2
      | LandA (t1, t2) -> aux t1 @ aux t2
      | SeqA (t1, t2) -> aux t1 @ aux t2
      | StarA t -> aux t
      | ComplementA t -> aux t
    in
    aux regex

  (* gather lits *)

  let gather regex =
    let rec aux regex m =
      match regex with
      | EmptyA -> m
      | AnyA -> m
      | EpsilonA -> m
      | EventA se -> SE.gather m se
      | LorA (t1, t2) -> aux t1 @@ aux t2 m
      | SetMinusA (t1, t2) -> aux t1 @@ aux t2 m
      | LandA (t1, t2) -> aux t1 @@ aux t2 m
      | SeqA (t1, t2) -> aux t1 @@ aux t2 m
      | StarA t -> aux t m
      | ComplementA t -> aux t m
    in
    aux regex (SE.gathered_lits_init ())

  (* normalize name *)

  let normalize_name regex =
    let rec aux regex =
      match regex with
      | AnyA | EmptyA | EpsilonA -> regex
      | EventA se -> EventA (SE.normalize_name se)
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | SetMinusA (t1, t2) -> SetMinusA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
      | ComplementA t -> ComplementA (aux t)
    in
    aux regex

  let close_fv x regex =
    let rec aux regex =
      match regex with
      | AnyA | EmptyA | EpsilonA -> regex
      | EventA se -> EventA (SE.close_fv x se)
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | SetMinusA (t1, t2) -> SetMinusA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
      | ComplementA t -> ComplementA (aux t)
    in
    aux regex

  (* TODO: stat *)
  let stat_size regex =
    let rec aux regex =
      match regex with
      | EmptyA | EpsilonA -> 0
      | AnyA | EventA _ -> 1
      | LorA (t1, t2) -> aux t1 + aux t2
      | SetMinusA (t1, t2) -> 1 + aux t1 + aux t2
      | LandA (t1, t2) -> 1 + aux t1 + aux t2
      | SeqA (t1, t2) -> aux t1 + aux t2
      | StarA t -> 1 + aux t
      | ComplementA t -> 1 + aux t
    in
    aux regex
end
