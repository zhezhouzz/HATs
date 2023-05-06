open Languages
open Sugar
open Ntyped
open NSimpleTypectx
open Zzdatatype.Datatype

let infer_id ctx name =
  (* let () = *)
  (*   Printf.printf "[infer_id] ctx: %s\n" @@ List.split_by_comma fst ctx *)
  (* in *)
  match get_opt ctx name.x with
  | None -> failwith @@ spf "free variable (%s) in refinement type" name.x
  | Some (_, ty) -> { ty; x = name.x }

let rec infer_lit ctx lit =
  let open Autov.Prop in
  match lit with
  | AVar id -> AVar (infer_id ctx id)
  | ACint _ | ACbool _ -> lit
  | AOp2 (mp, a, b) ->
      let a = infer_lit ctx a in
      let b = infer_lit ctx b in
      if NT.eq (lit_get_ty a) Ty_int && NT.eq (lit_get_ty b) Ty_int && is_op mp
      then AOp2 (mp, a, b)
      else _failatwith __FILE__ __LINE__ ""

let infer_prop ctx t =
  let open Autov.Prop in
  let rec aux ctx t =
    match t with
    | Lit lit -> Lit (infer_lit ctx lit)
    | Implies (e1, e2) -> Implies (aux ctx e1, aux ctx e2)
    | Ite (e1, e2, e3) -> Ite (aux ctx e1, aux ctx e2, aux ctx e3)
    | Not e -> Not (aux ctx e)
    | And es -> And (List.map (aux ctx) es)
    | Or es -> Or (List.map (aux ctx) es)
    | Iff (e1, e2) -> Iff (aux ctx e1, aux ctx e2)
    | MethodPred (mp, args) -> MethodPred (mp, List.map (infer_lit ctx) args)
    | Forall (u, e) ->
        let ctx = add_to_right ctx (u.x, u.ty) in
        Forall (u, aux ctx e)
    | Exists (u, e) ->
        (* let () = Printf.printf "ADD %s\n" u.x in *)
        let ctx = add_to_right ctx (u.x, u.ty) in
        Exists (u, aux ctx e)
  in
  aux ctx t

module Ntyped = Languages.Ntyped

let to_ctx qvs = List.map Ntyped.(fun x -> (x.x, x.ty)) qvs

open UT

let ot_infer ctx { basename; normalty; prop } =
  let ctx = add_to_right ctx (basename, normalty) in
  { basename; normalty; prop = infer_prop ctx prop }

let infer uqvs t =
  (* let () = *)
  (*   Printf.printf "%s infer: %s\n" *)
  (*     (List.split_by_comma (fun x -> spf "(%s:%s)" x.x @@ NT.layout x.ty) uqvs) *)
  (*   @@ Frontend.Underty.pretty_layout t *)
  (* in *)
  let rec aux ctx = function
    | UnderTy_base { basename; normalty; prop } ->
        let ctx = add_to_right ctx (basename, normalty) in
        UnderTy_base { basename; normalty; prop = infer_prop ctx prop }
    | UnderTy_under_arrow { argty; retty } ->
        let argty = aux ctx argty in
        (* let () = *)
        (*   Printf.printf "[infer] ctx: %s\n" @@ List.split_by_comma fst ctx *)
        (* in *)
        UnderTy_under_arrow { argty; retty = aux ctx retty }
    | UnderTy_over_arrow { argname; argty; retty } ->
        let argty = ot_infer ctx argty in
        let ctx = add_to_right ctx (argname, argty.normalty) in
        UnderTy_over_arrow { argname; argty; retty = aux ctx retty }
    | UnderTy_tuple ts ->
        let rec loop ctx = function
          | [] -> []
          | ty :: ts ->
              let ty = aux ctx ty in
              ty :: loop ctx ts
        in
        UnderTy_tuple (loop ctx ts)
  in
  aux (to_ctx uqvs) t
