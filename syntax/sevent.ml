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

  (* TODO: gather lits/rtys *)

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

  (* TODO: stat *)
end
