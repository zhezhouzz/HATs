open Languages
open Ntyped
open Sugar
open Autov
open Zzdatatype.Datatype

type t = (string * UT.t) list

let empty = []

(* let _update { ctx; pre } = *)
(*   let m = List.map (fun x -> (x.x, x.ty)) ctx in *)
(*   let pre = Undertycheck.infer_prop m pre in *)
(*   { ctx; pre } *)

let to_string ctx =
  spf "%s => "
    (List.split_by_comma
       (fun (x, ty) -> spf "∀ (%s:%s)" x (UT.pretty_layout ty))
       ctx)

let add_to_right ctx (id, ty) =
  (* let () = Pp.printf "@{<bold>Current: %s@} + %s\n" (to_string ctx) id in *)
  let ctx' =
    match List.find_opt (fun (id', _) -> String.equal id id') ctx with
    | None -> (
        match UT.erase ty with
        | Ty_int -> ctx @ [ (id, ty) ]
        | nt -> _failatwith __FILE__ __LINE__ (NT.layout nt))
    | Some _ -> _failatwith __FILE__ __LINE__ ""
  in
  ctx'

(* let add_pre ctx prop = *)
(*   (\* let () = Pp.printf "@{<bold>Current: %s@}\n" (to_string ctx) in *\) *)
(*   { ctx with pre = Prop.(peval (And [ ctx.pre; prop ])) } *)

let to_prop ctx =
  let xs, props =
    List.split
    @@ List.map
         (fun (x, ty) ->
           match UT.assume_base_destruct_opt ty with
           | Some (name, nt, prop) ->
               let prop = Prop.subst_id prop name x in
               ({ x; ty = nt }, prop)
           | None -> _failatwith __FILE__ __LINE__ "")
         ctx
  in
  (xs, Prop.(peval (And props)))

let get_ty ctx id =
  match List.find_opt (fun (x, _) -> String.equal id x) ctx with
  | None -> _failatwith __FILE__ __LINE__ (spf "cannot find: %s" id)
  | Some (_, ty) -> ty

let get_by_nt (ctx : t) nt =
  List.filter_map
    (fun (x, ty) ->
      if eq nt (UT.erase ty) then Some Ntyped.{ x; ty = nt } else None)
    ctx
(* let pre_subst_id { ctx; pre } x y = { ctx; pre = Prop.subst_id pre x y } *)

let type_infer ctx ty =
  let m = List.map (fun (x, ty) -> Ntyped.{ x; ty = UT.erase ty }) ctx in
  Undertycheck.infer m ty
