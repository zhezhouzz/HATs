open Language
module RCtx = RTypectx
module ROpCtx = ROpTypectx
module R = Rty
open Nt
open Sugar

(* let do_stat comp rty = *)
(*   let num_branchs = TypedCoreEff.stat_count_comp_branchs comp in *)
(*   let num_vars = TypedCoreEff.stat_count_comp_vars comp in *)
(*   let num_events = Rty.stat_num_events_rty rty in *)
(*   let num_lits = List.length @@ Rty.stat_lits_from_rty_no_dup rty in *)
(*   let is_rec = TypedCoreEff.stat_is_rec comp in *)
(*   let stat = *)
(*     Stat.init (is_rec, num_vars, num_branchs, num_effects, num_events, num_lits) *)
(*   in *)
(*   let () = Smtquery.stat_init () in *)
(*   let () = Baux.stat_init () in *)
(*   let () = Desymbolic.stat_init () in *)
(*   () *)

let pprint_res_one (id, res, timef) =
  match res with
  | Some _ ->
      Pp.printf
        "@{<bold>Task %i:@} exec time @{<bold>%f(s)@}, @{<bold>@{<yellow>type \
         check succeeded@}@}\n"
        id timef
  | None ->
      Pp.printf
        "@{<bold>Task %i:@} exec time @{<bold>%f(s)@}, @{<bold>@{<red>type \
         check failed@}@}\n"
        id timef

(* let pprint_res = List.iter pprint_res_one *)

let check (opctx', rctx') structure normalized_structure =
  (* let () = *)
  (*   Printf.printf "Structure:\n%s\n" @@ Structure.layout_structure structure *)
  (* in *)
  let opctx, rctx = ROpCtx.from_code structure in
  let opctx = opctx' @ opctx in
  let rctx = rctx' @ rctx in
  (* let num_effects = List.length opctx in *)
  (* let eqctx = Eqctx.from_code structure in *)
  (* let () = Printf.printf "!!! %s\n" @@ Eqctx.layout_equations eqctx in *)
  (* let () = failwith "end" in *)
  let tasks = RTypectx.get_task structure in
  let ress =
    List.mapi
      (fun id (name, rty) ->
        let id = id + 1 in
        let () =
          Env.show_debug_typing @@ fun _ -> Pp.printf "@{<bold>Task %i:@}\n" id
        in
        match
          List.find_opt
            (fun (name', _) -> String.equal name name')
            normalized_structure
        with
        | None -> _failatwith __FILE__ __LINE__ ""
        | Some (_, comp) ->
            let () =
              if not (Nt.eq comp.ty (R.erase_rty rty)) then
                let () =
                  Printf.printf
                    "The erased type of the refinement type mismacted the \
                     implementation:\n\
                     %s (rty) !=\n\
                     %s (imp)\n"
                    (Nt.layout (R.erase_rty rty))
                    (Nt.layout comp.ty)
                in
                _failatwith __FILE__ __LINE__ "input error"
              else ()
            in
            (* let () = Printf.printf "%s\n" @@ R.layout_rty rty in *)
            (* let () = failwith "end" in *)
            (* let () = do_stat comp rty in *)
            let typecheck_time, res =
              Sugar.clock (fun () ->
                  Bidirectional.comp_type_check { rctx; opctx } comp (R.Rty rty))
            in
            (* let stat = *)
            (*   Stat.update_dynamic_stat stat typecheck_time *)
            (*     (Smtquery.stat_get_cur ()) (Baux.stat_get_cur ()) *)
            (*     (Desymbolic.stat_get_cur ()) *)
            (* in *)
            let () =
              Env.show_debug_typing @@ fun _ ->
              pprint_res_one (id, res, typecheck_time)
            in
            (* let elrond_stat_record = Infer_ghost.get_stat () in *)
            (* let () = *)
            (*   Printf.printf "len: %i\n" (List.length elrond_stat_record); *)
            (*   failwith "end" *)
            (* in *)
            (* let stat = Stat.update_elrond stat elrond_stat_record in *)
            (id, res, typecheck_time))
      tasks
  in
  ress
