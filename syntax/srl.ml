module F (L : Lit.T) = struct
  (* open Sexplib.Std *)
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

  type sfa_len = EmptySet | HasUniqLen of int | MayNoUniqLen

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

  let rec simpl r =
    match r with
    | EventA (GuardEvent phi) when is_true phi -> AnyA
    | EventA (GuardEvent phi) when is_false phi -> EmptyA
    | EmptyA | EpsilonA | AnyA | EventA _ -> r
    | LorA (r1, r2) -> (
        let r1, r2 = map2 simpl (r1, r2) in
        match (has_len_aux r1, has_len_aux r2) with
        | EmptySet, _ -> r2
        | _, EmptySet -> r1
        | _ -> LorA (r1, r2))
    | LandA (r1, r2) -> (
        let r1, r2 = map2 simpl (r1, r2) in
        match (has_len_aux r1, has_len_aux r2) with
        | EmptySet, _ | _, EmptySet -> EmptyA
        | _ -> (
            match (r1, r2) with
            | AnyA, _ -> be_singleton r2
            | _, AnyA -> be_singleton r1
            | _, _ -> LandA (r1, r2)))
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

  (* let rec is_one_len a = *)
  (*   match a with *)
  (*   | EmptyA -> false *)
  (*   | EpsilonA -> true *)
  (*   | AnyA | EventA _ -> Some a *)
  (*   | LorA (a1, a2) -> *)
  (*     (is_zero_len a1) && (is_zero_len a2) *)
  (*   | LandA (a1, a2) -> *)
  (*     (is_zero_len a1) || (is_zero_len a2) *)
  (*   | SeqA (a1, a2) -> *)
  (*     (is_zero_len a1) && (is_zero_len a2) *)
  (*   | StarA a -> is_zero_len a *)
  (*   | ComplementA _ -> false *)
  (*   | SetMinusA (a1, a2) -> is_empty a1 && is_empty a2 *)

  (* let rec to_singleton a = *)
  (*   match a with *)
  (*   | EmptyA | EpsilonA | AnyA | EventA _ -> Some a *)
  (*   | LorA (a1, a2) -> *)
  (*     let* a1 = to_singleton a1 in *)
  (*     let* a2 = to_singleton a2 in *)
  (*     Some (LorA (a1, a2)) *)
  (*   | LandA (a1, a2) -> *)
  (*     let* a1 = to_singleton a1 in *)
  (*     let* a2 = to_singleton a2 in *)
  (*     Some (LandA (a1, a2)) *)
  (*   | SeqA (a1, ) *)

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

  (* TODO: gather lits/rtys *)

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

  (* TODO: stat *)
end
