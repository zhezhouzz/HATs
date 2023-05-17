module type CtxType = sig
  type t

  (* val mk_noty : 'a -> 'a typed *)
  (* val ( #: ) : 'a -> t -> 'a typed *)

  (* val ( #-> ) : ('a -> 'b) -> 'a typed -> 'b typed *)
  val layout : t -> string
  (* val layout_typed_l : ('a -> string) -> 'a typed list -> string *)

  (* val is_basic_tp : t -> bool *)
  (* val is_dt : t -> bool *)
  (* val eq : t -> t -> bool *)

  (* val destruct_arr_tp : t -> t list * t *)
  (* val construct_arr_tp : t list * t -> t *)
  (* val default_ty : t *)
  (* val _type_unify : string -> int -> t -> t -> t *)
end

module type CtxId = sig
  type ctxid

  val equal : ctxid -> ctxid -> bool
  val layout : ctxid -> string
end

module StrId = struct
  type ctxid = string

  let equal = String.equal
  let layout x = x
end

module OpId = struct
  type ctxid = Op.t

  let equal = Op.eq
  let layout = Op.to_string
end

module F (I : CtxId) (Ty : CtxType) = struct
  open Zzdatatype.Datatype

  (* open Sexplib.Std *)
  open Sugar
  open Ty

  type binding = I.ctxid * t
  type ctx = binding list

  let last_destruct_opt pctx =
    let* l, (x, ty) = List.last_destruct_opt pctx in
    Some (l, (x, ty))

  let layout_typed f (x, ty) = spf "%s:%s" (f x) (layout ty)

  let layout_typed_l f l =
    Zzdatatype.Datatype.List.split_by_comma (layout_typed f) l

  let from_kv_list l = l
  let empty = []
  let exists ctx name = List.exists (fun (x, _) -> I.equal x name) ctx
  (* let get_opctx ctx = List.filter (fun x -> Op.id_is_dt x.x) ctx *)

  let get_ty_opt (ctx : ctx) id : t option =
    match List.find_opt (fun (x, _) -> I.equal id x) ctx with
    | None -> None
    | Some (_, ty) -> Some ty

  let get_ty (ctx : ctx) id : t =
    match get_ty_opt ctx id with
    | None ->
        _failatwith __FILE__ __LINE__
        @@ spf "no such name (%s) in the type context" (I.layout id)
    | Some ty -> ty

  let new_to_right ctx (x, ty) =
    if exists ctx x then
      _failatwith __FILE__ __LINE__ (spf "Add %s" (I.layout x))
    else ctx @ [ (x, ty) ]

  let new_to_rights ctx l = List.fold_left new_to_right ctx l
  let fold_right = List.fold_right
  let fold_left = List.fold_left
  let filter_map = List.filter_map
  let pretty_layout ctx = List.split_by "\n" (layout_typed I.layout) ctx

  let pretty_print ctx =
    Env.show_debug_typing (fun _ ->
        if List.length ctx == 0 then Pp.printf "@{<green>∅@}\n"
        else
          List.iter
            (fun (x, ty) ->
              Pp.printf "%s:@{<green>%s@}," (I.layout x) (layout ty))
            ctx)

  let pretty_print_lines ctx =
    Env.show_debug_typing (fun _ ->
        if List.length ctx == 0 then Pp.printf "@{<green>∅@}\n"
        else
          List.iter
            (fun (x, ty) ->
              Pp.printf "%s:@{<green>%s@}\n" (I.layout x) (layout ty))
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

module FString (Ty : CtxType) = struct
  include F (StrId) (Ty)
end

module FOp (Ty : CtxType) = struct
  include F (OpId) (Ty)
end
