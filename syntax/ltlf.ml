module F (L : Lit.T) = struct
  (* open Sexplib.Std *)
  module SRL = Srl.F (L)
  include SRL

  type ltlf =
    | EventL of sevent
    | LorL of ltlf * ltlf
    | LandL of ltlf * ltlf
    | SeqL of ltlf * ltlf
    | NegL of ltlf
    | NextL of ltlf
    | UntilL of ltlf * ltlf
    | LastL
    | FinalL of ltlf
    | GlobalL of ltlf
  [@@deriving sexp]

  type sfa = ltlf [@@deriving sexp]

  open Sugar

  let compare l1 l2 = Sexplib.Sexp.compare (sexp_of_ltlf l1) (sexp_of_ltlf l2)
  let eq l1 l2 = 0 == compare l1 l2

  (* syntax sugar *)
  let _topL = EventL (GuardEvent mk_true)
  let _lastL = NegL (NextL _topL)

  let to_final_opt = function
    | UntilL (a1, a2) -> if eq _topL a1 then Some a2 else None
    | _ -> None

  let to_global_opt = function
    | NegL (UntilL (a1, NegL a2)) -> if eq _topL a1 then Some a2 else None
    | _ -> None

  let is_last = eq _lastL

  let to_singleton_opt = function
    | LandL (a1, a2) ->
        if is_last a1 then Some a2 else if is_last a2 then Some a1 else None
    | _ -> None

  let rec desugar (ltlf : ltlf) =
    match ltlf with
    | EventL _ -> ltlf
    | LastL -> _lastL
    | FinalL ltlf -> UntilL (_topL, desugar ltlf)
    | GlobalL ltlf -> NegL (UntilL (_topL, NegL (desugar ltlf)))
    | NegL a -> NegL (desugar a)
    | LorL (a1, a2) -> LorL (desugar a1, desugar a2)
    | LandL (a1, a2) -> LandL (desugar a1, desugar a2)
    | SeqL (a1, a2) -> SeqL (desugar a1, desugar a2)
    | NextL a -> NextL (desugar a)
    | UntilL (a1, a2) -> UntilL (desugar a1, desugar a2)

  let rec ensugar (ltlf : ltlf) =
    match ltlf with
    | EventL _ -> ltlf
    | LastL -> ltlf
    | FinalL ltlf -> FinalL (ensugar ltlf)
    | GlobalL ltlf -> GlobalL (ensugar ltlf)
    | NegL a -> NegL (ensugar a)
    | LorL (a1, a2) -> LorL (ensugar a1, ensugar a2)
    | LandL (a1, a2) -> LandL (ensugar a1, ensugar a2)
    | SeqL (a1, a2) -> SeqL (ensugar a1, ensugar a2)
    | NextL a -> NextL (ensugar a)
    | UntilL (a1, a2) -> UntilL (ensugar a1, ensugar a2)

  let rec to_srl_aux (a : ltlf) : regex =
    match a with
    | EventL sevent -> SeqA (EventA sevent, mk_regex_all)
    | LastL -> AnyA
    | GlobalL (EventL se) -> StarA (EventA se)
    | GlobalL a ->
        let a' = to_srl_aux a in
        if has_len a' 0 then EmptyA
        else if has_len a' 1 then StarA a'
        else to_srl_aux (NegL (FinalL (NegL a)))
    | FinalL a -> SeqA (StarA AnyA, to_srl_aux a)
    | NegL a -> ComplementA (to_srl_aux a)
    | LorL (a1, a2) -> LorA (to_srl_aux a1, to_srl_aux a2)
    (* | LandL (LastL, a2) -> *)
    (*     let a2 = to_srl_aux a2 in *)
    (*     if has_len a2 1 then a2 else LandA (to_srl_aux LastL, a2) *)
    (* | LandL (a1, LastL) -> *)
    (*     let a1 = to_srl_aux a1 in *)
    (*     if has_len a1 1 then a1 else LandA (to_srl_aux LastL, a1) *)
    | LandL (a1, a2) -> LandA (to_srl_aux a1, to_srl_aux a2)
    | SeqL (a1, a2) -> SeqA (to_srl_aux a1, to_srl_aux a2)
    | NextL a -> SeqA (AnyA, to_srl_aux a)
    | UntilL (a, a2) ->
        let a = to_srl_aux a in
        let a2 = to_srl_aux a2 in
        if has_len a 0 then a2
        else if has_len a 1 then SeqA (StarA a, a2)
        else _failatwith __FILE__ __LINE__ "unimp until"

  let to_srl (a : ltlf) : regex = simpl @@ to_srl_aux a
end
