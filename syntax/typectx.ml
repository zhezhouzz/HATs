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

module F (I : CtxId) = struct
  open Zzdatatype.Datatype

  (* open Sexplib.Std *)
  open Sugar

  type 'a binding = I.ctxid * 'a
  type 'a poly_ctx = 'a binding list

  let last_destruct_opt pctx =
    let* l, (x, ty) = List.last_destruct_opt pctx in
    Some (l, (x, ty))

  let layout_typed f (x, ty) = spf "%s:%s" (I.layout x) (f ty)

  let layout_typed_l f l =
    Zzdatatype.Datatype.List.split_by_comma (layout_typed f) l

  let from_kv_list l = l
  let empty = []
  let exists ctx name = List.exists (fun (x, _) -> I.equal x name) ctx
  (* let get_opctx ctx = List.filter (fun x -> Op.id_is_dt x.x) ctx *)

  let get_ty_opt (ctx : 'a poly_ctx) id : 'a option =
    match List.find_opt (fun (x, _) -> I.equal id x) ctx with
    | None -> None
    | Some (_, ty) -> Some ty

  let get_ty (ctx : 'a poly_ctx) id : 'a =
    match get_ty_opt ctx id with
    | None ->
        _failatwith __FILE__ __LINE__
        @@ spf "no such name (%s) in the type context" (I.layout id)
    | Some ty -> ty

  let new_to_right ctx (x, ty) =
    if exists ctx x then
      _failatwith __FILE__ __LINE__ (spf "Add repeat binding %s" (I.layout x))
    else ctx @ [ (x, ty) ]

  let new_to_rights ctx l = List.fold_left new_to_right ctx l
  let fold_right = List.fold_right
  let fold_left = List.fold_left
  let filter_map = List.filter_map
  let pretty_layout f ctx = List.split_by "\n" (layout_typed f) ctx

  let pretty_print f ctx =
    Env.show_debug_typing (fun _ ->
        if List.length ctx == 0 then Pp.printf "@{<green>∅@}\n"
        else
          List.iter
            (fun (x, ty) -> Pp.printf "%s:@{<green>%s@}," (I.layout x) (f ty))
            ctx)

  let pretty_print_lines f ctx =
    Env.show_debug_typing (fun _ ->
        if List.length ctx == 0 then Pp.printf "@{<green>∅@}\n"
        else
          List.iter
            (fun (x, ty) -> Pp.printf "%s:@{<green>%s@}\n" (I.layout x) (f ty))
            ctx)

  let pretty_layout_judge ctx (e, ty) =
    Printf.sprintf "%s⊢\n%s :\n%s\n" ctx e ty

  let pretty_layout_subtyping ctx (r1, r2) =
    Printf.sprintf "%s⊢\n%s <:\n%s\n" ctx r1 r2

  let pretty_print_infer f ctx (e, (r : 'a)) =
    Env.show_debug_typing (fun _ ->
        let () = Pp.printf "@{<bold>Type Infer:@}\n" in
        pretty_print f ctx;
        Pp.printf "⊢ @{<hi_magenta>%s@} ⇨ " (short_str 100 e);
        Pp.printf "@{<cyan>%s@}\n\n" @@ f r)

  let pretty_print_judge f ctx (e, (r : 'a)) =
    Env.show_debug_typing (fun _ ->
        let () = Pp.printf "@{<bold>Type Check:@}\n" in
        pretty_print f ctx;
        Pp.printf "⊢ @{<hi_magenta>%s@} ⇦ " (short_str 10000 e);
        Pp.printf "@{<cyan>%s@}\n\n" @@ f r)
end

module FString = struct
  include F (StrId)
end

module FOp = struct
  include F (OpId)
end
