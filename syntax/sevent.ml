module F (L : Lit.T) = struct
  open Sexplib.Std
  module Cty = Cty.F (L)
  include Cty

  type sevent =
    | GuardEvent of prop
    | EffEvent of {
        op : string;
        vs : string typed list;
        v : string typed;
        phi : prop;
      }
  [@@deriving sexp]

  open Sugar
  open Common

  let vs_names_from_types tps =
    let n = List.length tps in
    let vs = vs_names n in
    List.map (fun (x, ty) -> x #: ty) @@ _safe_combine __FILE__ __LINE__ vs tps

  (* subst *)

  let subst (y, z) sevent =
    match sevent with
    | GuardEvent phi -> GuardEvent (subst_prop (y, z) phi)
    | EffEvent { op; vs; v; phi } ->
        if List.exists (fun x -> String.equal x.x y) (v :: vs) then
          EffEvent { op; vs; v; phi }
        else EffEvent { op; vs; v; phi = subst_prop (y, z) phi }

  let subst_id (y, z) rty =
    let z = AVar z in
    subst (y, z) rty

  (* fv *)

  let fv sevent =
    match sevent with
    | GuardEvent phi -> fv_prop phi
    | EffEvent { vs; phi; v; _ } ->
        List.filter (fun y ->
            not (List.exists (fun x -> String.equal x.x y) (v :: vs)))
        @@ fv_prop phi

  (* gather lits *)

  open Zzdatatype.Datatype

  type gathered_lits = {
    global_lits : lit list;
    local_lits : (string typed list * lit list) StrMap.t;
  }

  let gathered_lits_init () = { global_lits = []; local_lits = StrMap.empty }

  let gathered_rm_dup { global_lits; local_lits } =
    let global_lits = List.slow_rm_dup eq_lit global_lits in
    let local_lits =
      StrMap.map
        (fun (vs, lits) -> (vs, List.slow_rm_dup eq_lit lits))
        local_lits
    in
    { global_lits; local_lits }

  let gather { global_lits; local_lits } sevent =
    match sevent with
    | GuardEvent phi ->
        { global_lits = P.get_lits phi @ global_lits; local_lits }
    | EffEvent { op; phi; vs; v } ->
        let lits = P.get_lits phi in
        let vs' = List.map (fun x -> x.x) (v :: vs) in
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
              | None -> Some (v :: vs, llits)
              | Some (_, l) -> Some (v :: vs, l @ llits))
            local_lits
        in
        let global_lits = global_lits @ glits in
        { global_lits; local_lits }

  (* normalize name *)

  let normalize_name = function
    | GuardEvent phi -> GuardEvent phi
    | EffEvent { op; vs; v; phi } ->
        let vs' = vs_names (List.length vs) in
        let tmp =
          _safe_combine __FILE__ __LINE__ (v :: vs) (v_ret_name :: vs')
        in
        let phi =
          List.fold_left
            (fun phi (x', x) -> P.subst_prop_id (x'.x, x) phi)
            phi tmp
        in
        let vs, v =
          match List.map (fun (v, x) -> { x; ty = v.ty }) tmp with
          | [] -> _failatwith __FILE__ __LINE__ "die"
          | v :: vs -> (vs, v)
        in
        EffEvent { op; vs; v; phi }

  (* unify name *)

  let close_fv x sevent =
    match sevent with
    | GuardEvent phi -> GuardEvent (close_fv x phi)
    | EffEvent { op; vs; v; phi } ->
        EffEvent { op; vs; v; phi = close_fv x phi }

  (* TODO: stat *)
end
