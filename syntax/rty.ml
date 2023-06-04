module F (L : Lit.T) = struct
  open Sexplib.Std
  include Cty.F (L)

  type arr_kind = SigamArr | PiArr [@@deriving sexp]

  let eq_arr_kind k1 k2 =
    match (k1, k2) with
    | SigamArr, SigamArr -> true
    | PiArr, PiArr -> true
    | _, _ -> false

  type pty =
    | BasePty of { cty : cty }
    | TuplePty of pty list
    | ArrPty of {
        arr_kind : arr_kind;
        rarg : string option ptyped;
        retrty : rty;
      }

  and rty =
    | Pty of pty
    | Regty of { nty : Nt.t; prereg : regex; postreg : regex }
  [@@deriving sexp]

  and sevent =
    | GuardEvent of prop
    | RetEvent of pty
    | EffEvent of { op : string; vs : string Nt.typed list; phi : prop }

  and regex =
    | EmptyA
    | EpsilonA
    | AnyA
    | EventA of sevent
    | LorA of regex * regex
    | LandA of regex * regex
    | SeqA of regex * regex
    | StarA of regex
    | ComplementA of regex
  [@@deriving sexp]

  and 'a ptyped = { px : 'a; pty : pty } [@@deriving sexp]

  type 'a rtyped = { rx : 'a; rty : rty }

  open Sugar

  let mk_regex_any = AnyA
  let mk_regex_all = StarA AnyA

  let smart_seq (a1, a2) =
    match a1 with EmptyA -> EmptyA | EpsilonA -> a2 | _ -> SeqA (a1, a2)

  let str_eq_to_bv y x =
    match x with Some x -> String.equal x y | None -> false

  let ret_name = "Ret"
  let guard_name = "Guard"
  let vs_names n = List.init n (fun i -> spf "%s%i" v_name i)

  let vs_names_from_types tps =
    let n = List.length tps in
    let vs = vs_names n in
    List.map (fun (x, ty) -> x #: ty) @@ _safe_combine __FILE__ __LINE__ vs tps

  (* NOTE: Gurad is not a real event, thus it has no op name *)
  let se_get_op = function
    | RetEvent _ -> ret_name
    | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
    | EffEvent { op; _ } -> op

  let se_force_op = function
    | RetEvent _ -> _failatwith __FILE__ __LINE__ "die"
    | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
    | EffEvent { op; vs; phi } -> (op, vs, phi)

  let pty_destruct_arr = function
    | ArrPty { arr_kind = PiArr; rarg; retrty } -> (rarg, retrty)
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let rty_force_pty = function
    | Pty pty -> pty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let pty_force_cty = function
    | BasePty { cty } -> cty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let rty_force_cty rty = rty |> rty_force_pty |> pty_force_cty
  let compare_pty l1 l2 = Sexplib.Sexp.compare (sexp_of_pty l1) (sexp_of_pty l2)
  let eq_pty l1 l2 = 0 == compare_pty l1 l2

  let compare_rty tau1 tau2 =
    Sexplib.Sexp.compare (sexp_of_rty tau1) (sexp_of_rty tau2)

  let eq_rty tau1 tau2 = 0 == compare_rty tau1 tau2
  let ( #:: ) px pty = { px; pty }
  let ( #--> ) f { px; pty } = { px = f px; pty }

  (* subst *)

  let rec subst_pty (y, z) rty =
    let rec aux rty =
      match rty with
      | BasePty { cty } -> BasePty { cty = subst_cty (y, z) cty }
      | TuplePty ptys -> TuplePty (List.map aux ptys)
      | ArrPty { arr_kind; rarg; retrty } ->
          let rarg = rarg.px #:: (aux rarg.pty) in
          if str_eq_to_bv y rarg.px then ArrPty { arr_kind; rarg; retrty }
          else ArrPty { arr_kind; rarg; retrty = subst (y, z) retrty }
    in
    aux rty

  and subst_sevent (y, z) sevent =
    match sevent with
    | GuardEvent phi -> GuardEvent (subst_prop (y, z) phi)
    | RetEvent pty -> RetEvent (subst_pty (y, z) pty)
    | EffEvent { op; vs; phi } ->
        if List.exists (fun x -> String.equal x.Nt.x y) vs then
          EffEvent { op; vs; phi }
        else EffEvent { op; vs; phi = subst_prop (y, z) phi }

  and subst_regex (y, z) regex =
    let rec aux regex =
      match regex with
      | EmptyA -> EmptyA
      | AnyA -> AnyA
      | EpsilonA -> EpsilonA
      | EventA se -> EventA (subst_sevent (y, z) se)
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
      | ComplementA t -> ComplementA (aux t)
    in
    aux regex

  and subst (y, z) = function
    | Pty pty -> Pty (subst_pty (y, z) pty)
    | Regty { nty; prereg; postreg } ->
        Regty
          {
            nty;
            prereg = subst_regex (y, z) prereg;
            postreg = subst_regex (y, z) postreg;
          }

  let subst_rty = subst

  let subst_id (y, z) rty =
    let z = AVar z in
    subst (y, z) rty

  let subst_regex_id (y, z) rty =
    let z = AVar z in
    subst_regex (y, z) rty

  (* fv *)

  let rec fv_pty rty =
    let rec aux rty =
      match rty with
      | BasePty { cty; _ } -> fv_cty cty
      | TuplePty ptys -> List.concat_map aux ptys
      | ArrPty { rarg; retrty; _ } ->
          let argfv = aux rarg.pty in
          let retfv =
            List.filter (fun x -> not (str_eq_to_bv x rarg.px)) @@ fv retrty
          in
          argfv @ retfv
    in
    aux rty

  and fv_sevent sevent =
    match sevent with
    | GuardEvent phi -> fv_prop phi
    | RetEvent pty -> fv_pty pty
    | EffEvent { vs; phi; _ } ->
        List.filter (fun y ->
            not (List.exists (fun x -> String.equal x.Nt.x y) vs))
        @@ fv_prop phi

  and fv_regex regex =
    let rec aux regex =
      match regex with
      | EmptyA -> []
      | AnyA -> []
      | EpsilonA -> []
      | EventA se -> fv_sevent se
      | LorA (t1, t2) -> aux t1 @ aux t2
      | LandA (t1, t2) -> aux t1 @ aux t2
      | SeqA (t1, t2) -> aux t1 @ aux t2
      | StarA t -> aux t
      | ComplementA t -> aux t
    in
    aux regex

  and fv = function
    | Pty pty -> fv_pty pty
    | Regty { prereg; postreg; _ } -> fv_regex prereg @ fv_regex postreg

  (* erase *)

  let rec erase_pty rty =
    let open Nt in
    let rec aux rty =
      match rty with
      | BasePty { cty; _ } -> erase_cty cty
      | TuplePty ptys -> Ty_tuple (List.map aux ptys)
      | ArrPty { rarg; retrty; arr_kind = PiArr } ->
          mk_arr (aux rarg.pty) (erase retrty)
      | ArrPty { retrty; arr_kind = SigamArr; _ } -> erase retrty
    in
    aux rty

  and erase = function Pty pty -> erase_pty pty | Regty { nty; _ } -> nty

  let ptyped_opt_erase { px; pty } =
    match px with None -> None | Some x -> Some Nt.{ x; ty = erase_pty pty }

  let ptyped_erase { px; pty } = Nt.{ x = px; ty = erase_pty pty }

  let pty_to_ret_rty pty =
    Regty
      {
        nty = erase_pty pty;
        prereg = StarA AnyA;
        postreg = EventA (RetEvent pty);
      }

  let rtyped_force_to_ptyped file line { rx; rty } =
    match rty with
    | Pty pty -> { px = rx; pty }
    | _ -> _failatwith file line "die"

  (* gather lits/rtys *)

  open Zzdatatype.Datatype

  type gathered_lits = {
    global_lits : lit list;
    global_pty : pty list;
    local_lits : (string Nt.typed list * lit list) StrMap.t;
  }

  let gathered_lits_init () =
    { global_lits = []; global_pty = []; local_lits = StrMap.empty }

  let gathered_rm_dup { global_lits; global_pty; local_lits } =
    let global_lits = List.slow_rm_dup eq_lit global_lits in
    let global_pty = List.slow_rm_dup eq_pty global_pty in
    let local_lits =
      StrMap.map
        (fun (vs, lits) -> (vs, List.slow_rm_dup eq_lit lits))
        local_lits
    in
    { global_lits; global_pty; local_lits }

  let gather_from_sevent { global_lits; global_pty; local_lits } sevent =
    match sevent with
    | GuardEvent phi ->
        { global_lits = P.get_lits phi @ global_lits; global_pty; local_lits }
    | RetEvent pty ->
        { global_lits; global_pty = pty :: global_pty; local_lits }
    | EffEvent { op; phi; vs } ->
        let lits = P.get_lits phi in
        let vs' = List.map (fun x -> x.Nt.x) vs in
        let is_contain_local_free lit =
          match List.interset ( == ) vs' @@ P.fv_lit lit with
          | [] -> false
          | _ -> true
        in
        let llits, glits = List.partition is_contain_local_free lits in
        let local_lits =
          StrMap.update op
            (fun l ->
              match l with
              | None -> Some (vs, llits)
              | Some (_, l) -> Some (vs, l @ llits))
            local_lits
        in
        let global_lits = global_lits @ glits in
        { global_lits; global_pty; local_lits }

  let gather_from_regex regex =
    let rec aux regex m =
      match regex with
      | EmptyA -> m
      | AnyA -> m
      | EpsilonA -> m
      | EventA se -> gather_from_sevent m se
      | LorA (t1, t2) -> aux t1 @@ aux t2 m
      | LandA (t1, t2) -> aux t1 @@ aux t2 m
      | SeqA (t1, t2) -> aux t1 @@ aux t2 m
      | StarA t -> aux t m
      | ComplementA t -> aux t m
    in
    aux regex (gathered_lits_init ())

  (* let get_lits_from_sevent sevent = *)
  (*   match sevent with *)
  (*   | GuardEvent phi -> *)
  (*       let global_lits = P.get_lits phi in *)
  (*       Some (guard_name, global_lits, []) *)
  (*   | RetEvent _ -> None *)
  (*   | EffEvent { op; phi; vs } -> *)
  (*       let vs = List.map (fun x -> x.Nt.x) vs in *)
  (*       let is_contain_local_free lit = *)
  (*         match List.interset ( == ) vs @@ P.fv_lit lit with *)
  (*         | [] -> false *)
  (*         | _ -> true *)
  (*       in *)
  (*       let lits = P.get_lits phi in *)
  (*       let local_lits, global_lits = *)
  (*         List.partition is_contain_local_free lits *)
  (*       in *)
  (*       Some (op, global_lits, local_lits) *)

  (* let get_lits_from_regex regex = *)
  (*   let update_local m (op, lits) = *)
  (*     StrMap.update op *)
  (*       (fun lits' -> *)
  (*         match lits' with *)
  (*         | None -> Some lits *)
  (*         | Some lits' -> Some (List.slow_rm_dup P.eq_lit (lits @ lits'))) *)
  (*       m *)
  (*   in *)
  (*   let update_global m lits = List.slow_rm_dup P.eq_lit (lits @ m) in *)
  (*   let rec aux regex (global_m, local_m) = *)
  (*     match regex with *)
  (*     | EpsilonA -> (global_m, local_m) *)
  (*     | EventA se -> ( *)
  (*         match get_lits_from_sevent se with *)
  (*         | None -> (global_m, local_m) *)
  (*         | Some (op, global_lits, _) when String.equal op guard_name -> *)
  (*             (update_global global_m global_lits, local_m) *)
  (*         | Some (op, global_lits, local_lits) -> *)
  (*             ( update_global global_m global_lits, *)
  (*               update_local local_m (op, local_lits) )) *)
  (*     | LorA (t1, t2) -> aux t1 @@ aux t2 (global_m, local_m) *)
  (*     | LandA (t1, t2) -> aux t1 @@ aux t2 (global_m, local_m) *)
  (*     | SeqA (t1, t2) -> aux t1 @@ aux t2 (global_m, local_m) *)
  (*     | StarA t -> aux t (global_m, local_m) *)
  (*   in *)
  (*   aux regex ([], StrMap.empty) *)

  (* let get_ptys_from_sevent sevent = *)
  (*   match sevent with RetEvent pty -> [ pty ] | _ -> [] *)

  (* let get_ptys_from_regex regex = *)
  (*   let rec aux regex res = *)
  (*     match regex with *)
  (*     | EpsilonA -> res *)
  (*     | EventA se -> res @ get_ptys_from_sevent se *)
  (*     | LorA (t1, t2) -> aux t1 @@ aux t2 res *)
  (*     | LandA (t1, t2) -> aux t1 @@ aux t2 res *)
  (*     | SeqA (t1, t2) -> aux t1 @@ aux t2 res *)
  (*     | StarA t -> aux t res *)
  (*   in *)
  (*   List.slow_rm_dup eq_pty @@ aux regex [] *)

  (* normalize name *)

  let rec normalize_name_pty tau1 =
    match tau1 with
    | BasePty { cty } -> BasePty { cty = normalize_name_cty cty }
    | TuplePty tys -> TuplePty (List.map normalize_name_pty tys)
    | ArrPty { arr_kind; rarg; retrty } ->
        let rarg = rarg.px #:: (normalize_name_pty rarg.pty) in
        let retrty = normalize_name_rty retrty in
        ArrPty { arr_kind; rarg; retrty }

  and normalize_name_sevent = function
    | GuardEvent phi -> GuardEvent phi
    | RetEvent pty -> RetEvent (normalize_name_pty pty)
    | EffEvent { op; vs; phi } ->
        let vs' = vs_names (List.length vs) in
        let tmp = _safe_combine __FILE__ __LINE__ vs vs' in
        let phi =
          List.fold_left
            (fun phi (x', x) -> P.subst_prop_id (x'.Nt.x, x) phi)
            phi tmp
        in
        let vs = List.map (fun (v, x) -> Nt.{ x; ty = v.ty }) tmp in
        EffEvent { op; vs; phi }

  and noralize_name_regex regex =
    let rec aux regex =
      match regex with
      | AnyA | EmptyA | EpsilonA -> regex
      | EventA se -> EventA (normalize_name_sevent se)
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
      | ComplementA t -> ComplementA (aux t)
    in
    aux regex

  and normalize_name_rty tau =
    match tau with
    | Pty tau -> Pty (normalize_name_pty tau)
    | Regty { nty; prereg; postreg } ->
        Regty
          {
            nty;
            prereg = noralize_name_regex prereg;
            postreg = noralize_name_regex postreg;
          }

  (* unify name *)

  let rec unify_name_pty (tau1, tau2) =
    match (tau1, tau2) with
    | BasePty _, BasePty _ -> (tau1, tau2)
    | TuplePty tys1, TuplePty tys2 ->
        let tys1, tys2 =
          List.split @@ List.map unify_name_pty
          @@ _safe_combine __FILE__ __LINE__ tys1 tys2
        in
        (TuplePty tys1, TuplePty tys2)
    | ( ArrPty { arr_kind = k1; rarg = rarg1; retrty = retrty1 },
        ArrPty { arr_kind = k2; rarg = rarg2; retrty = retrty2 } )
      when eq_arr_kind k1 k2 ->
        let pty1, pty2 = unify_name_pty (rarg1.pty, rarg2.pty) in
        let (rarg1, rarg2), retrty2 =
          match (rarg1.px, rarg2.px) with
          | None, None -> ((None #:: pty1, None #:: pty2), retrty2)
          | Some x1, Some x2 ->
              ( ((Some x1) #:: pty1, (Some x1) #:: pty2),
                subst_id (x2, x1) retrty2 )
          | _, _ -> _failatwith __FILE__ __LINE__ "?"
        in
        let retrty1, retrty2 = unify_name_rty (retrty1, retrty2) in
        ( ArrPty { arr_kind = k1; rarg = rarg1; retrty = retrty1 },
          ArrPty { arr_kind = k2; rarg = rarg2; retrty = retrty2 } )
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  and unify_name_rty (tau1, tau2) =
    match (tau1, tau2) with
    | Pty tau1, Pty tau2 ->
        let tau1, tau2 = unify_name_pty (tau1, tau2) in
        (Pty tau1, Pty tau2)
    | Regty _, Regty _ -> (tau1, tau2)
    | Pty tau1, Regty _ -> unify_name_rty (pty_to_ret_rty tau1, tau2)
    | Regty _, Pty tau2 -> unify_name_rty (tau1, pty_to_ret_rty tau2)
  (* | _, _ -> _failatwith __FILE__ __LINE__ "?" *)

  let mk_unit_pty_from_prop phi = BasePty { cty = mk_unit_cty_from_prop phi }
  let mk_unit_rty_from_prop phi = Pty (mk_unit_pty_from_prop phi)
  let default_ty = mk_unit_rty_from_prop mk_true
  let xmap f { x; ty } = { x = f x; ty }
  let is_base_pty = function BasePty _ -> true | _ -> false

  (* regular expression *)

  let delimited_reverse regex =
    let rec aux regex =
      match regex with
      | AnyA | EmptyA | EpsilonA | EventA _ -> regex
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t2, aux t1)
      | StarA t -> StarA (aux t)
      | ComplementA t -> ComplementA (aux t)
    in
    aux regex

  (* mk bot/top *)

  let rec mk_bot_pty t =
    match t with
    | Nt.Ty_arrow (t1, t2) ->
        let px =
          match t1 with
          | Nt.Ty_arrow (_, _) -> None
          | _ -> Some (Rename.unique "x")
        in
        let pty = mk_top_pty t1 in
        let retrty = Pty (mk_bot_pty t2) in
        ArrPty { arr_kind = PiArr; rarg = { px; pty }; retrty }
    | Nt.Ty_tuple tys -> TuplePty (List.map mk_bot_pty tys)
    | _ -> BasePty { cty = mk_bot_cty t }

  and mk_top_pty t =
    match t with
    | Nt.Ty_arrow (t1, t2) ->
        let px =
          match t1 with
          | Nt.Ty_arrow (_, _) -> None
          | _ -> Some (Rename.unique "x")
        in
        let pty = mk_bot_pty t1 in
        let retrty = Pty (mk_top_pty t2) in
        ArrPty { arr_kind = PiArr; rarg = { px; pty }; retrty }
    | Nt.Ty_tuple tys -> TuplePty (List.map mk_top_pty tys)
    | _ -> BasePty { cty = mk_top_cty t }

  let is_arr_pty = function
    | ArrPty { arr_kind = PiArr; _ } -> true
    | _ -> false

  (* dummy interfaces *)
  let is_basic_tp _ = _failatwith __FILE__ __LINE__ "never happen"
  let is_dt _ = _failatwith __FILE__ __LINE__ "never happen"
  let destruct_arr_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let construct_arr_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify _ _ = _failatwith __FILE__ __LINE__ "unimp"
  let to_smttyped _ = _failatwith __FILE__ __LINE__ "unimp"
  let typed_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_typed _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify_ _ = _failatwith __FILE__ __LINE__ "unimp"

  let destruct_arr_one rty =
    match rty with
    | ArrPty { arr_kind = PiArr; rarg; retrty } -> (rarg, retrty)
    | _ -> _failatwith __FILE__ __LINE__ ""

  let get_argty rty =
    match rty with
    | Pty rty ->
        let rarg, _ = destruct_arr_one rty in
        Pty rarg.pty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let get_retty rty =
    match rty with
    | Pty rty ->
        let _, retrty = destruct_arr_one rty in
        retrty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let snd_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let fst_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let bool_ty = default_ty
  let mk_tuple _ = _failatwith __FILE__ __LINE__ "unimp"
  let mk_arr _ = _failatwith __FILE__ __LINE__ "unimp"
  let int_ty = default_ty
  let unit_pty = BasePty { cty = mk_unit_cty_from_prop mk_true }
  let unit_ty = Pty unit_pty
  let to_smtty _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_t _ = _failatwith __FILE__ __LINE__ "unimp"
  let t_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
end
