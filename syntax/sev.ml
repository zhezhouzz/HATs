module F (L : Lit.T) = struct
  open Common
  open Sexplib.Std
  include Cty.F (L)

  type sev = {
    op : string;
    vs : string Nt.typed list;
    v : string Nt.typed;
    phi : prop;
  }
  [@@deriving sexp]

  open Sugar

  (* subst *)
  let subst_sev (y, z) { op; vs; v; phi } =
    if List.exists (fun x -> String.equal x.Nt.x y) (v :: vs) then
      { op; vs; v; phi }
    else { op; vs; v; phi = subst_prop (y, z) phi }

  (* fv *)

  and fv_sev { vs; phi; v; _ } =
    List.filter (fun y ->
        not (List.exists (fun x -> String.equal x.Nt.x y) (v :: vs)))
    @@ fv_prop phi

  (* normalize name *)

  let normalize_name_sev { op; vs; v; phi } =
    let vs' = vs_names (List.length vs) in
    let tmp = _safe_combine __FILE__ __LINE__ (v :: vs) (v_ret_name :: vs') in
    let phi =
      List.fold_left
        (fun phi (x', x) -> P.subst_prop_id (x'.Nt.x, x) phi)
        phi tmp
    in
    let vs, v =
      match List.map (fun (v, x) -> Nt.{ x; ty = v.ty }) tmp with
      | [] -> _failatwith __FILE__ __LINE__ "die"
      | v :: vs -> (vs, v)
    in
    EffEvent { op; vs; v; phi }
end
