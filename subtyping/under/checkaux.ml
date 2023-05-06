open Languages
open Sugar
module P = Autov.Prop

let check_empty_hidden file line hvs =
  if List.length hvs != 0 then
    _failatwith file line "do not allow hidden variables"
  else ()

open Abstraction
open Zzdatatype.Datatype

let unify file line underfty normalty =
  let open UT in
  let open Ntyped in
  let rec aux m = function
    | UnderTy_base { basename; normalty; prop }, nt ->
        let m, normalty = NT._type_unify_ file line m normalty nt in
        let prop = P.type_update m prop in
        UnderTy_base { basename; normalty; prop }
    | UnderTy_over_arrow { argname; argty; retty }, Ty_arrow (t1, t2) ->
        let m, _ = NT._type_unify_ file line m argty.normalty t1 in
        let retty = aux m (retty, t2) in
        UnderTy_over_arrow { argname; argty; retty }
    | UnderTy_under_arrow { argty; retty }, Ty_arrow (t1, t2) ->
        let argty = aux m (argty, t1) in
        let retty = aux m (retty, t2) in
        UnderTy_under_arrow { argty; retty }
    | UnderTy_tuple uts, Ty_tuple ts ->
        let l = _safe_combine file line uts ts in
        UnderTy_tuple (List.map (aux m) l)
    | _, _ -> _failatwith file line "unify"
  in
  aux StrMap.empty (underfty, normalty)

let erase_check_mk_id file line id underfty =
  (* let () = *)
  (*   Pp.printf "|_ %s _| ~> %s = %s\n" *)
  (*     (Frontend.Underty.layout underfty) *)
  (*     (Frontend.Type.layout @@ UT.erase underfty) *)
  (*     (Frontend.Type.layout id.NL.ty) *)
  (* in *)
  let ty = unify file line underfty (snd id.NL.ty) in
  UL.{ ty; x = id.x }
(* let _ = _check_equality file line NT.eq (UT.erase underfty) (snd id.NL.ty) in *)
(* UL.{ ty = underfty; x = id.x } *)

(* let subtyping_check__with_hidden_vars = *)
(*   Undersub.subtyping_check_with_hidden_vars *)

let merge_case_tys tys =
  let ty = UT.disjunct_list tys in
  ty

include Underctx

(* let full_projection_check uctx fty = *)
(*   match uctx.rec_info with *)
(*   | None -> _failatwith __FILE__ __LINE__ "" *)
(*   | Some { rank_lhs; _ } -> ( *)
(*       let () = Pp.printf "Full Projection Check:\n" in *)
(*       let right_ty = UT.map_by_ghost_name fty (rank_lhs, fun _ -> None) in *)
(*       let left_ty = UT.reduce_inv_type_by_name fty rank_lhs in *)
(*       try *)
(*         let () = Inv_check.check (left_ty, right_ty) in *)
(*         Pp.printf "@{<bold>@{<yellow>Full Projection Check successed@}@}\n" *)
(*       with Autov.FailWithModel (msg, e) -> *)
(*         Pp.printf "@{<bold>@{<red>Full Projection Check failed@}@}\n"; *)
(*         raise (Autov.FailWithModel (msg, e))) *)

(* let if_rec_call uctx fname argname = *)
(*   match (uctx.rec_info, fname) with *)
(*   | None, _ -> false *)
(*   | _, None -> false *)
(*   | Some { fix_name; rank_lhs; _ }, Some fname -> *)
(*       let () = Pp.printf "@{<bold>if_rec_call %s  %s@}\n" fix_name fname in *)
(*       String.equal fname fix_name && String.equal argname rank_lhs *)

(* let if_rec_function uctx fname = *)
(*   match uctx.rec_info with *)
(*   | None -> false *)
(*   | Some { fix_name; _ } -> String.equal fname fix_name *)

(* let if_rec_measure_arg uctx argname = *)
(*   match uctx.rec_info with *)
(*   | None -> false *)
(*   | Some { rank_lhs; _ } -> String.equal rank_lhs argname *)

(* let right_ty_measure_0 uctx ty = *)
(*   match uctx.rec_info with *)
(*   | None -> _failatwith __FILE__ __LINE__ "" *)
(*   | Some { rank_lhs; _ } -> *)
(*       UT.map_by_ghost_name ty *)
(*         ( rank_lhs, *)
(*           fun { basename; normalty; prop } -> *)
(*             let prop = *)
(*               P.( *)
(*                 let x = Ntyped.{ x = basename; ty = normalty } in *)
(*                 let prop' = MethodPred ("==", [ ACint 0; AVar x ]) in *)
(*                 And [ prop; prop' ]) *)
(*             in *)
(*             Some { basename; normalty; prop } ) *)

(* let right_ty_measure_ind uctx ty = *)
(*   match uctx.rec_info with *)
(*   | None -> _failatwith __FILE__ __LINE__ "" *)
(*   | Some { rank_lhs; _ } -> *)
(*       UT.map_by_ghost_name ty *)
(*         ( rank_lhs, *)
(*           fun { basename; normalty; prop } -> *)
(*             let prop = *)
(*               P.( *)
(*                 let x = Ntyped.{ x = basename; ty = normalty } in *)
(*                 And [ prop; MethodPred ("<", [ ACint 0; AVar x ]) ]) *)
(*             in *)
(*             Some { basename; normalty; prop } ) *)

(* let left_ty_measure_0 uctx ty = *)
(*   match uctx.rec_info with *)
(*   | None -> _failatwith __FILE__ __LINE__ "" *)
(*   | Some { rank_lhs; _ } -> *)
(*       UT.map_by_ghost_name ty *)
(*         ( rank_lhs, *)
(*           fun { basename; normalty; _ } -> *)
(*             Some { basename; normalty; prop = P.mk_false } ) *)

(* let left_ty_measure_i uctx ty = *)
(*   match uctx.rec_info with *)
(*   | None -> _failatwith __FILE__ __LINE__ "" *)
(*   | Some { rank_lhs; _ } -> *)
(*       UT.map_by_ghost_name ty *)
(*         ( rank_lhs, *)
(*           fun { basename; normalty; prop } -> *)
(*             Some *)
(*               { *)
(*                 basename; *)
(*                 normalty; *)
(*                 prop = *)
(*                   P.( *)
(*                     let x = Ntyped.{ x = basename; ty = normalty } in *)
(*                     And [ prop; MethodPred ("<", [ ACint 0; AVar x ]) ]); *)
(*               } ) *)

(* let synthesize_ghost_term uctx = *)
(*   match uctx.rec_info with *)
(*   | None -> _failatwith __FILE__ __LINE__ "" *)
(*   | Some { rank_lhs; _ } -> *)
(*       let n = Ntyped.{ x = rank_lhs; ty = Ty_int } in *)
(*       let ty = *)
(*         UT.make_basic_from_prop Ty_int (fun v -> *)
(*             P.(MethodPred ("==", [ AVar v; AOp2 ("-", AVar n, ACint 1) ]))) *)
(*       in *)
(*       let rank_lhs' = Rename.unique rank_lhs in *)
(*       UL.{ x = rank_lhs'; ty } *)

(* let candidate_vars_by_nt uctx nt = *)
(*   let cs = Typectx.get_by_nt uctx.ctx nt in *)
(*   List.filter_map *)
(*     (fun (x, ty) -> *)
(*       match ty with *)
(*       | MMT.Consumed _ -> None *)
(*       | MMT.NoRefinement _ -> None *)
(*       | MMT.Ut ty -> *)
(*           Some (x, ty) *)
(*           (\* let b = Reachability_check.reachability_check uctx.ctx ty in *\) *)
(*           (\* if b then Some x else None *\) *)
(*       | MMT.Ot ty -> *)
(*           (\* TODO: check ot *\) *)
(*           Some (x, UT.ot_to_ut ty)) *)
(*     cs *)

open UT

(* let handle_consume uctx (args, uty) = *)
(*   let rec aux = function *)
(*     | [], _ -> [] *)
(*     | _ :: args, UnderTy_over_arrow { retty; _ } -> aux (args, retty) *)
(*     | arg :: args, UnderTy_under_arrow { retty; _ } -> *)
(*         arg.UL.x :: aux (args, retty) *)
(*     | _, _ -> _failatwith __FILE__ __LINE__ "" *)
(*   in *)
(*   let consumed_vars = aux (args, uty) in *)
(*   let ctx = *)
(*     List.fold_left *)
(*       (fun ctx arg -> Typectx.consume ctx arg) *)
(*       uctx.ctx consumed_vars *)
(*   in *)
(*   { uctx with ctx } *)

let term_subtyping_check file line uctx UL.{ x; ty } t2 =
  let () = Undersub.subtyping_check file line uctx.ctx ty t2 in
  UL.{ x; ty = t2 }

let term_subtyping_check_opt file line uctx UL.{ x; ty } t2 =
  if Undersub.subtyping_check_bool file line uctx.ctx ty t2 then
    Some UL.{ x; ty = t2 }
  else None

(* let make_eq_type (id, idty) = *)
(*   let id = Ntyped.{ x = id.NL.x; ty = snd id.NL.ty } in *)
(*   match id.ty with *)
(*   | NT.Ty_unit -> idty *)
(*   | _ -> *)
(*       if NT.is_basic_tp id.ty then make_basic_from_eq_var id *)
(*       else if NT.is_dt id.ty then *)
(*         (\* HACK: assume the dt type will not change; when there is not pattern matching *\) *)
(*         if true then idty *)
(*         else *)
(*           let all_mps = *)
(*             match !Env.config with *)
(*             | None -> _failatwith __FILE__ __LINE__ "" *)
(*             | Some config -> config.all_mps *)
(*           in *)
(*           let () = Pp.printf "all_mps: %s\n" @@ StrList.to_string all_mps in *)
(*           Dt_eq.make_eq_type all_mps id *)
(*       else idty *)

let ut_eq_to_ut_underctx (uctx : uctx) t =
  match t with
  | MMT.UtNormal t -> t
  | MMT.UtCopy id -> (
      match Typectx.get_ty uctx.ctx id.NTyped.x with
      | Ot _ -> make_basic_from_eq_var id
      | Ut (UtNormal idty) ->
          if NT.is_basic_tp id.ty then make_basic_from_eq_var id
          else if NT.is_dt id.ty then
            (* HACK: assume the dt type will not change; when there is not pattern matching *)
            if true then idty
            else
              let all_mps =
                match !Env.config with
                | None -> _failatwith __FILE__ __LINE__ ""
                | Some config -> config.all_mps
              in
              let () =
                Env.show_debug_debug @@ fun _ ->
                Pp.printf "all_mps: %s\n" @@ StrList.to_string all_mps
              in
              Dt_eq.make_eq_type all_mps id
          else idty
      | _ -> _failatwith __FILE__ __LINE__ "")

let subtyping_check file line uctx t1 t2 =
  let t1 = ut_eq_to_ut_underctx uctx t1 in
  Undersub.subtyping_check file line uctx.ctx t1 t2

let subtyping_check_bool file line uctx t1 t2 =
  let t1 = ut_eq_to_ut_underctx uctx t1 in
  Undersub.subtyping_check_bool file line uctx.ctx t1 t2

let id_type_infer (uctx : uctx) (id : NL.id NL.typed) : MMT.ut_with_copy =
  let () = Env.show_debug_debug @@ fun _ -> Pp.printf "infer %s\n" id.x in
  try MMT.UtNormal (Prim.get_primitive_under_ty (id.x, snd id.ty))
  with _ -> (
    try MMT.UtNormal (Nctx.get_ty uctx.libctx id.x)
    with _ -> (
      match Typectx.get_ty uctx.ctx id.x with
      | Ot _ -> MMT.UtCopy { x = id.x; ty = snd id.ty }
      | Ut (UtCopy id) -> MMT.UtCopy id
      | Ut (UtNormal uty) ->
          if UT.is_base_type uty then
            match UT.erase uty with
            | NT.Ty_unit -> UtNormal uty
            | _ -> MMT.UtCopy { x = id.x; ty = snd id.ty }
          else UtNormal uty
      | Consumed _ -> _err_consumed __FILE__ __LINE__ id.x))

let id_type_check (uctx : uctx) (id : NL.id NL.typed) (ty : UT.t) : unit =
  let id = id_type_infer uctx id in
  subtyping_check __FILE__ __LINE__ uctx id ty

let lit_type_infer (lit : NL.smt_lit) : UL.t =
  let open NL in
  let open UT in
  match lit with
  | ConstI n -> make_basic_from_const_int n
  | ConstB b -> make_basic_from_const_bool b

let close_ids ids ty = Typectx.close_by_diff_ ids ty

let make_order_constraint a x ty =
  let open NT in
  match ty with
  | Ty_int ->
      P.(
        And
          [
            MethodPred ("<", [ AVar { x; ty }; AVar { x = a; ty } ]);
            MethodPred (">=", [ AVar { x; ty }; ACint 0 ]);
          ])
  | _ -> _failatwith __FILE__ __LINE__ "unimp"

let dt_expand f argsty =
  let measure =
    match !Env.config with
    | None -> _failatwith __FILE__ __LINE__ ""
    | Some c -> c.measure
  in
  let argsty =
    List.concat
    @@ List.map
         (fun uty ->
           if NT.is_dt (MMT.ut_erase_ uty) then
             match uty with
             | UtNormal _ -> _failatwith __FILE__ __LINE__ "unimp"
             | UtCopy id ->
                 let sizeargty =
                   UT.make_basic_from_prop NT.Ty_int (fun v ->
                       P.(MethodPred (measure, [ AVar id; AVar v ])))
                 in
                 [ MMT.UtNormal sizeargty; uty ]
           else [ uty ])
         argsty
  in
  let fnty =
    let _, retnty = NT.destruct_arrow_tp (snd f.NL.ty) in
    let argsnty = List.map MMT.ut_erase_ argsty in
    NT.construct_arrow_tp (argsnty, retnty)
  in
  (fnty, argsty)
