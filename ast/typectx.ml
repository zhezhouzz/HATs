module type CtxType = sig
  type t
  type 'a typed = { x : 'a; ty : t }

  val mk_noty : 'a -> 'a typed
  val ( #: ) : 'a -> t -> 'a typed
  val xmap : ('a -> 'b) -> 'a typed -> 'b typed
  val layout : t -> string
  val layout_typed : ('a -> string) -> 'a typed -> string
  val layout_typed_l : ('a -> string) -> 'a typed list -> string
  val is_basic_tp : t -> bool
  val is_dt : t -> bool
  val eq : t -> t -> bool
  val destruct_arr_tp : t -> t list * t
  val construct_normal_tp : t list * t -> t
  val default_ty : t
  val _type_unify : string -> int -> t -> t -> t
  val is_eff_arr : t -> bool
end

module F (Ty : CtxType) = struct
  open Zzdatatype.Datatype

  (* open Sexplib.Std *)
  open Sugar
  open Ty

  type ctx = string typed list

  let empty = []
  let exists ctx name = List.exists (fun x -> String.equal x.x name) ctx

  let get_ty_opt (ctx : ctx) id : t option =
    match List.find_opt (fun x -> String.equal id x.x) ctx with
    | None -> None
    | Some x -> Some x.ty

  let get_effctx l = List.filter (fun x -> is_eff_arr x.ty) l

  let get_ty (ctx : ctx) id : t =
    match get_ty_opt ctx id with
    | None ->
        _failatwith __FILE__ __LINE__
        @@ spf "no such name (%s) in the type context" id
    | Some ty -> ty

  let new_to_right ctx { x; ty } =
    if exists ctx x then _failatwith __FILE__ __LINE__ (spf "Add %s" x)
    else ctx @ [ { x; ty } ]

  let new_to_rights ctx l = List.fold_left new_to_right ctx l
  let fold_right = List.fold_right
  let filter_map = List.filter_map
  let pretty_layout ctx = List.split_by "\n" (layout_typed (fun x -> x)) ctx

  let pretty_print ctx =
    Env.show_debug_typing (fun _ ->
        if List.length ctx == 0 then Pp.printf "@{<green>∅@}"
        else
          List.iter
            (fun x -> Pp.printf "%s:@{<green>%s@}," x.x (layout x.ty))
            ctx)

  let pretty_print_lines ctx =
    Env.show_debug_typing (fun _ ->
        if List.length ctx == 0 then Pp.printf "@{<green>∅@}"
        else
          List.iter
            (fun x -> Pp.printf "%s:@{<green>%s@}\n" x.x (layout x.ty))
            ctx)

  let pretty_layout_judge ctx (e, ty) =
    Printf.sprintf "%s⊢\n%s :\n%s\n" ctx e ty

  let pretty_layout_subtyping ctx (r1, r2) =
    Printf.sprintf "%s⊢\n%s <:\n%s\n" ctx r1 r2

  let pretty_print_infer ctx (e, (r : t)) =
    Env.show_debug_typing (fun _ ->
        let () = Pp.printf "@{<bold>Type Infer:@}\n" in
        pretty_print ctx;
        Pp.printf "⊢ @{<hi_magenta>%s@} ⇨ " (short_str 100 e);
        Pp.printf "@{<cyan>%s@}\n\n" @@ layout r)

  let pretty_print_judge ctx (e, (r : t)) =
    Env.show_debug_typing (fun _ ->
        let () = Pp.printf "@{<bold>Type Check:@}\n" in
        pretty_print ctx;
        Pp.printf "⊢ @{<hi_magenta>%s@} ⇦ " (short_str 10000 e);
        Pp.printf "@{<cyan>%s@}\n\n" @@ layout r)
end

module NTypectx = struct
  include F (Normalty.Ntyped)
  include Normalty.Ntyped
end
