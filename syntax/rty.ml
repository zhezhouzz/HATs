module F (L : Lit.T) = struct
  (* open Sexplib.Std *)
  module LTLf = Ltlf.F (L)
  module LRty = Rty_tree.SyntaxF (LTLf) (L)
  module SRL = LTLf.SRL
  include Rty_tree.SyntaxF (SRL) (L)
  include SRL

  let rec apply_pred_rty pred rty =
    let open LRty in
    match rty with
    | BaseRty _ -> rty
    | ArrRty { arr; rethty } ->
        ArrRty
          { arr = apply_pred_arr pred arr; rethty = apply_pred_hty pred rethty }

  and apply_pred_arr pred arr =
    let open LRty in
    match arr with
    | NormalArr { rx; rty } -> NormalArr { rx; rty = apply_pred_rty pred rty }
    | GhostArr _ -> arr
    | ArrArr rty -> ArrArr (apply_pred_rty pred rty)

  and apply_pred_hty pred hty =
    let open LRty in
    match hty with
    | Rty rty -> Rty (apply_pred_rty pred rty)
    | Htriple { pre; resrty; post } ->
        Htriple
          {
            pre = LTLf.apply_pred pred pre;
            resrty = apply_pred_rty pred resrty;
            post = LTLf.apply_pred pred post;
          }
    | Inter (hty1, hty2) ->
        Inter (apply_pred_hty pred hty1, apply_pred_hty pred hty2)

  let rec to_hty = function
    | LRty.Rty rty -> Rty (to_rty rty)
    | LRty.Htriple { pre; resrty; post } ->
        Htriple
          {
            pre = LTLf.to_srl pre;
            resrty = to_rty resrty;
            post = LTLf.to_srl post;
          }
    | LRty.Inter (hty1, hty2) -> Inter (to_hty hty1, to_hty hty2)

  and to_arr = function
    | LRty.NormalArr { rx; rty } -> NormalArr { rx; rty = to_rty rty }
    | LRty.GhostArr x -> GhostArr x
    | LRty.ArrArr rty -> ArrArr (to_rty rty)

  and to_rty = function
    | LRty.BaseRty { cty } -> BaseRty { cty }
    | LRty.ArrRty { arr; rethty } ->
        ArrRty { arr = to_arr arr; rethty = to_hty rethty }

  let eq_arr_kind k1 k2 =
    match (k1, k2) with
    | NormalArr _, NormalArr _ -> true
    | GhostArr _, GhostArr _ -> true
    | ArrArr _, ArrArr _ -> true
    | _, _ -> false

  open Sugar
  (* open Common *)

  let hty_force_rty = function
    | Rty rty -> rty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let rty_force_cty = function
    | BaseRty { cty } -> cty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let hty_force_cty rty = rty |> hty_force_rty |> rty_force_cty
  let compare_rty l1 l2 = Sexplib.Sexp.compare (sexp_of_rty l1) (sexp_of_rty l2)
  let compare_hty l1 l2 = Sexplib.Sexp.compare (sexp_of_hty l1) (sexp_of_hty l2)
  let eq_rty l1 l2 = 0 == compare_rty l1 l2
  let eq_hty l1 l2 = 0 == compare_hty l1 l2
  let ( #:: ) rx rty = { rx; rty }

  (* subst *)

  let arr_get_name_opt = function
    | NormalArr { rx; _ } -> Some rx
    | GhostArr Nt.{ x; _ } -> Some x
    | ArrArr _ -> None

  let rec subst_rty (y, z) rty =
    let aux rty =
      match rty with
      | BaseRty { cty } -> BaseRty { cty = Cty.subst (y, z) cty }
      | ArrRty { arr; rethty } -> (
          let arr = subst_arr (y, z) arr in
          match arr_get_name_opt arr with
          | Some x when String.equal x y -> ArrRty { arr; rethty }
          | _ -> ArrRty { arr; rethty = subst_hty (y, z) rethty })
    in
    aux rty

  and subst_arr (y, z) = function
    | NormalArr { rx; rty } -> NormalArr { rx; rty = subst_rty (y, z) rty }
    | GhostArr garg -> GhostArr garg
    | ArrArr rty -> ArrArr (subst_rty (y, z) rty)

  and subst_hty (y, z) = function
    | Rty rty -> Rty (subst_rty (y, z) rty)
    | Htriple { pre; resrty; post } ->
        Htriple
          {
            pre = SRL.subst (y, z) pre;
            resrty = subst_rty (y, z) resrty;
            post = SRL.subst (y, z) post;
          }
    | Inter (hty1, hty2) -> Inter (subst_hty (y, z) hty1, subst_hty (y, z) hty2)

  let subst_rty_id (y, z) rty =
    let z = AVar z in
    subst_rty (y, z) rty

  let subst_hty_id (y, z) rty =
    let z = AVar z in
    subst_hty (y, z) rty

  (* fv *)

  let rec fv_rty rty =
    match rty with
    | BaseRty { cty; _ } -> Cty.fv cty
    | ArrRty { arr; rethty } ->
        let argfv = fv_arr arr in
        let retfv = fv_hty rethty in
        let retfv =
          match arr_get_name_opt arr with
          | None -> retfv
          | Some x -> List.filter (fun y -> not (String.equal x y)) retfv
        in
        argfv @ retfv

  and fv_arr = function
    | NormalArr { rty; _ } -> fv_rty rty
    | GhostArr _ -> []
    | ArrArr rty -> fv_rty rty

  and fv_hty = function
    | Rty rty -> fv_rty rty
    | Htriple { pre; resrty; post } ->
        let pre_fv = SRL.fv pre in
        let resrty_fv = fv_rty resrty in
        let post_fv = SRL.fv post in
        pre_fv @ resrty_fv @ post_fv
    | Inter (hty1, hty2) -> fv_hty hty1 @ fv_hty hty2

  (* (\* erase *\) *)

  (* let rec erase_rty rty = *)
  (*   let open Nt in *)
  (*   match rty with *)
  (*   | BaseRty { cty; _ } -> Cty.erase cty *)
  (*   | ArrRty { arr; rethty } -> mk_arr (erase_arr arr) (erase_hty rethty) *)

  (* and erase_arr = function *)
  (*   | NormalArr { rty; _ } -> erase_rty rty *)
  (*   | GhostArr Nt.{ ty; _ } -> ty *)
  (*   | ArrArr rty -> erase_rty rty *)

  (* and erase_hty rty = *)
  (*   (\* let open Nt in *\) *)
  (*   match rty with *)
  (*   | Rty rty -> erase_rty rty *)
  (*   | Htriple { resrty; _ } -> erase_rty resrty *)
  (*   | Inter (hty1, hty2) -> *)
  (*       let ty1 = erase_hty hty1 in *)
  (*       let ty2 = erase_hty hty2 in *)
  (*       let _ = _assert __FILE__ __LINE__ "eq" (Nt.eq ty1 ty2) in *)
  (*       ty1 *)

  (* let rtyped_erase { rx; rty } = Nt.{ x = rx; ty = erase_rty rty } *)

  (* let rty_to_cty rty = *)
  (*   match rty with *)
  (*   | BaseRty { cty } -> cty *)
  (*   | _ -> _failatwith __FILE__ __LINE__ "die" *)

  (* let htyped_force_to_rtyped file line { hx; hty } = *)
  (*   match hty with *)
  (*   | Rty rty -> { rx = hx; rty } *)
  (*   | _ -> _failatwith file line "die" *)

  (* TODO: gather lits/rtys *)

  (* normalize name *)

  let rec normalize_name_rty tau1 =
    match tau1 with
    | BaseRty { cty } -> BaseRty { cty = Cty.normalize_name cty }
    | ArrRty { arr; rethty } ->
        ArrRty
          { arr = normalize_name_arr arr; rethty = normalize_name_hty rethty }

  and normalize_name_arr = function
    | NormalArr { rx; rty } -> NormalArr { rx; rty = normalize_name_rty rty }
    | GhostArr Nt.{ x; ty } -> GhostArr Nt.{ x; ty }
    | ArrArr rty -> ArrArr (normalize_name_rty rty)

  and normalize_name_hty tau =
    match tau with
    | Rty rty -> Rty (normalize_name_rty rty)
    | Htriple { pre; resrty; post } ->
        Htriple { pre; resrty = normalize_name_rty resrty; post }
    | Inter (hty1, hty2) ->
        let hty1 = normalize_name_hty hty1 in
        let hty2 = normalize_name_hty hty2 in
        Inter (hty1, hty2)

  (* unify name *)

  let rec unify_name_rty (tau1, tau2) =
    match (tau1, tau2) with
    | BaseRty _, BaseRty _ -> (tau1, tau2)
    | ( ArrRty { arr = arr1; rethty = rethty1 },
        ArrRty { arr = arr2; rethty = rethty2 } ) ->
        let arr1, arr2, sigma = unify_name_arr (arr1, arr2) in
        let rethty2 =
          match sigma with
          | None -> rethty2
          | Some (x, y) -> subst_hty_id (x, y) rethty2
        in
        let rethty1, rethty2 = unify_name_hty (rethty1, rethty2) in
        ( ArrRty { arr = arr1; rethty = rethty1 },
          ArrRty { arr = arr2; rethty = rethty2 } )
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  and unify_name_arr (arr1, arr2) =
    match (arr1, arr2) with
    | NormalArr { rx; rty }, NormalArr r2 ->
        (NormalArr { rx; rty }, NormalArr { rx; rty = r2.rty }, Some (r2.rx, rx))
    | GhostArr Nt.{ x; ty }, GhostArr g2 ->
        (GhostArr Nt.{ x; ty }, GhostArr Nt.{ x; ty = g2.ty }, Some (g2.Nt.x, x))
    | ArrArr rty1, ArrArr rty2 ->
        let rty1, rty2 = unify_name_rty (rty1, rty2) in
        (ArrArr rty1, ArrArr rty2, None)
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  and unify_name_hty (tau1, tau2) =
    match (tau1, tau2) with
    | Rty tau1, Rty tau2 ->
        let tau1, tau2 = unify_name_rty (tau1, tau2) in
        (Rty tau1, Rty tau2)
    | ( Htriple { pre = pre1; resrty = rty1; post = post1 },
        Htriple { pre = pre2; resrty = rty2; post = post2 } ) ->
        let rty1, rty2 = unify_name_rty (rty1, rty2) in
        ( Htriple { pre = pre1; resrty = rty1; post = post1 },
          Htriple { pre = pre2; resrty = rty2; post = post2 } )
    | Inter _, Inter _ -> (tau1, tau2)
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  let mk_unit_rty_from_prop phi = BaseRty { cty = Cty.mk_unit_from_prop phi }
  let mk_unit_hty_from_prop phi = Rty (mk_unit_rty_from_prop phi)
  let default_ty = mk_unit_rty_from_prop mk_true
  let xmap f { x; ty } = { x = f x; ty }
  let is_base_rty = function BaseRty _ -> true | _ -> false

  (* TODO: stat *)

  (* mk bot/top *)

  let rec mk_bot t =
    match t with
    | Nt.Ty_arrow (t1, t2) ->
        let rty = mk_top t1 in
        let arr =
          match t1 with
          | Nt.Ty_arrow (_, _) -> ArrArr rty
          | _ -> NormalArr { rx = Rename.unique "x"; rty }
        in
        ArrRty { arr; rethty = Rty (mk_bot t2) }
    | _ -> BaseRty { cty = Cty.mk_bot t }

  and mk_top t =
    match t with
    | Nt.Ty_arrow (t1, t2) ->
        let rty = mk_bot t1 in
        let arr =
          match t1 with
          | Nt.Ty_arrow (_, _) -> ArrArr rty
          | _ -> NormalArr { rx = Rename.unique "x"; rty }
        in
        ArrRty { arr; rethty = Rty (mk_top t2) }
    | _ -> BaseRty { cty = Cty.mk_top t }

  (* let is_arr_rty = function *)
  (*   | ArrRty { arr_kind = GhostArr; _ } -> true *)
  (*   | _ -> false *)

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
    | ArrRty { arr = NormalArr rarg; rethty } -> (rarg.rty, rethty)
    | ArrRty { arr = ArrArr rty; rethty } -> (rty, rethty)
    | _ -> _failatwith __FILE__ __LINE__ ""

  let get_argty rty =
    match rty with
    | Rty rty ->
        let rty, _ = destruct_arr_one rty in
        Rty rty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let get_retty rty =
    match rty with
    | Rty rty ->
        let _, rethty = destruct_arr_one rty in
        rethty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let snd_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let fst_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let bool_ty = default_ty
  let mk_tuple _ = _failatwith __FILE__ __LINE__ "unimp"
  let mk_arr _ = _failatwith __FILE__ __LINE__ "unimp"
  let int_ty = default_ty
  let unit_rty = BaseRty { cty = Cty.mk_unit_from_prop mk_true }
  let unit_ty = Rty unit_rty
  let to_smtty _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_t _ = _failatwith __FILE__ __LINE__ "unimp"
  let t_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
end
