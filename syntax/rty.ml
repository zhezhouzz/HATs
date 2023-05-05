module F (L : Lit.T) = struct
  module Nt = Lit.Ty
  module P = Qualifier.F (L)
  include P

  type cty = { v : string Nt.typed; phi : prop }
  type ou = Over | Under

  type pty =
    | BasePty of { ou : ou; cty : cty }
    | TuplePty of pty list
    | ArrPty of { rarg : string option ptyped; retrty : t }

  and t = Pty of pty | Regty of regex Nt.typed

  and sevent =
    | RetEvent of pty
    | EffEvent of { op : string; vs : string Nt.typed list; phi : prop }

  and regex =
    | EpsilonA
    | VarA of string
    | EventA of sevent
    | LorA of regex * regex
    | SeqA of regex * regex
    | StarA of regex
    | ExistsA of { localx : string ctyped; regex : regex }
    | RecA of { mux : string; muA : string; index : lit; regex : regex }

  and 'a ctyped = { cx : 'a; cty : cty }
  and 'a ptyped = { px : 'a; pty : pty }

  type 'a typed = { x : 'a; ty : t }

  let ou_eq a b =
    match (a, b) with Over, Over | Under, Under -> true | _ -> false

  let ou_flip = function Over -> Under | Under -> Over
  let ( #: ) x ty = { x; ty }
  let ( #:: ) px pty = { px; pty }
  let ( #::: ) cx cty = { cx; cty }
  let ( #-> ) f { x; ty } = { x = f x; ty }
  let ( #--> ) f { px; pty } = { px = f px; pty }
  let ( #---> ) f { cx; cty } = { cx = f cx; cty }

  let subst_cty (y, replacable) { v; phi } =
    if String.equal y v.Nt.x then { v; phi }
    else { v; phi = subst_prop (y, replacable) phi }

  let rec subst_pty (y, z) rty =
    let rec aux rty =
      match rty with
      | BasePty { cty; ou } -> BasePty { cty = subst_cty (y, z) cty; ou }
      | TuplePty ptys -> TuplePty (List.map aux ptys)
      | ArrPty { rarg; retrty } -> (
          let rarg = rarg.px #:: (aux rarg.pty) in
          match rarg.px with
          | Some x when String.equal y x -> ArrPty { rarg; retrty }
          | _ -> ArrPty { rarg; retrty = subst (y, z) retrty })
    in
    aux rty

  and subst_sevent (y, z) sevent =
    match sevent with
    | RetEvent pty -> RetEvent (subst_pty (y, z) pty)
    | EffEvent { op; vs; phi } ->
        if List.exists (fun x -> String.equal x.Nt.x y) vs then
          EffEvent { op; vs; phi }
        else EffEvent { op; vs; phi = subst_prop (y, z) phi }

  and subst_regex (y, z) regex =
    let rec aux regex =
      match regex with
      | VarA x -> VarA x
      | EpsilonA -> EpsilonA
      | EventA se -> EventA (subst_sevent (y, z) se)
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
      | ExistsA { localx; regex } ->
          if String.equal y localx.cx then ExistsA { localx; regex }
          else ExistsA { localx; regex = aux regex }
      | RecA { mux; muA; index; regex } ->
          let index = subst_lit (y, z) index in
          if String.equal y mux then RecA { mux; muA; index; regex }
          else RecA { mux; muA; index; regex = aux regex }
    in
    aux regex

  and subst (y, z) = function
    | Pty pty -> Pty (subst_pty (y, z) pty)
    | Regty regex -> Regty Nt.((subst_regex (y, z)) #-> regex)

  let subst_id (y, z) rty =
    let y = y.Nt.x in
    let z = AVar z in
    subst (y, z) rty

  let subst_cty_id (y, z) cty =
    let y = y.Nt.x in
    let z = AVar z in
    subst_cty (y, z) cty

  let regexsubst (y, z) regex =
    let rec aux regex =
      match regex with
      | VarA x -> if String.equal x y then z else VarA x
      | EpsilonA | EventA _ -> regex
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
      | ExistsA { localx; regex } -> ExistsA { localx; regex = aux regex }
      | RecA { mux; muA; index; regex } ->
          if String.equal y muA then RecA { mux; muA; index; regex }
          else RecA { mux; muA; index; regex = aux regex }
    in
    aux regex

  let erase_cty { v; _ } = v.Nt.ty

  open Sugar

  let rec erase_pty rty =
    let open Nt in
    let rec aux rty =
      match rty with
      | BasePty { cty; _ } -> erase_cty cty
      | TuplePty ptys -> Ty_tuple (List.map aux ptys)
      | ArrPty { rarg; retrty } -> mk_arr (aux rarg.pty) (erase retrty)
    in
    aux rty

  (* and erase_regex regex = *)
  (*   let open Nt in *)
  (*   let rec aux regex = *)
  (*     match regex with *)
  (*     | EpsilonA -> [] *)
  (*     | EventA (RetEvent pty) -> [ erase_pty pty ] *)
  (*     | EventA (EffEvent _) -> [] *)
  (*     | StarA t -> [] *)
  (*     | LorA (t1, t2) -> aux t1 @@ aux t2 *)
  (*     | SeqA (_, t2) -> aux t2 *)
  (*     | ExistsA { _; regex } -> aux regex *)
  (*   in *)
  (*   match aux regex with *)
  (*   | [] -> _failatwith __FILE__ __LINE__ "die" *)
  (*   | h :: t -> *)
  (*     if List.for_all (eq h) t then h else _failatwith __FILE__ __LINE__ "die" *)

  and erase = function Pty pty -> erase_pty pty | Regty regex -> regex.Nt.ty

  let ptyped_opt_erase { px; pty } =
    match px with None -> None | Some x -> Some Nt.{ x; ty = erase_pty pty }

  let typed_erase { x; ty } = Nt.{ x; ty = erase ty }

  let default_ty =
    Pty (BasePty { ou = Over; cty = Nt.{ v = "v" #: Ty_unit; phi = mk_true } })

  let mk_noty x = { x; ty = default_ty }
  let xmap f { x; ty } = { x = f x; ty }
  let is_basic_tp _ = _failatwith __FILE__ __LINE__ "never happen"
  let is_dt _ = _failatwith __FILE__ __LINE__ "never happen"

  (* TODO: imp eq *)
  let eq _ _ = false
  let destruct_arr_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let construct_arr_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify _ _ = _failatwith __FILE__ __LINE__ "unimp"
  let to_smttyped _ = _failatwith __FILE__ __LINE__ "unimp"
  let typed_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_typed _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify_ _ = _failatwith __FILE__ __LINE__ "unimp"

  let destruct_arr_one rty =
    match rty with
    | ArrPty { rarg; retrty } -> (rarg, retrty)
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

  let unit_pty =
    BasePty { ou = Under; cty = Nt.{ v = "v" #: Ty_unit; phi = mk_true } }

  let unit_ty = Pty unit_pty
  let to_smtty _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_t _ = _failatwith __FILE__ __LINE__ "unimp"
  let t_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
end
