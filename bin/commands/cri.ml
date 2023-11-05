open Core
open Caux
open Language

type inputs = {
  oppurenctx_files : string list;
  opeffnctx_files : string list;
  oppurerctx_files : string list;
  opeffrctx_files : string list;
  automata_pred_files : string list;
  rctx_files : string list;
      (* ri_files : string list; *)
      (* source_code : string; *)
}

let mk_inputs_setting meta_config_file =
  let () = Env.load_meta meta_config_file in
  {
    oppurenctx_files = [ Env.get_builtin_normal_type () ];
    opeffnctx_files = [];
    oppurerctx_files = [ Env.get_builtin_pure_type () ];
    opeffrctx_files = [ Env.get_builtin_eff_type () ];
    automata_pred_files = [ Env.get_builtin_automata_pred_type () ];
    rctx_files = [ Env.get_builtin_libfunc_type () ];
  }

type inputs_setting = {
  opnctx : (Op.t * Nt.t) list;
  automata_preds : StructureRaw.entry list;
  oprctx : (Op.t * Rty.rty) list;
  nctx : (string * Nt.t) list;
  rctx : (string * Rty.rty) list;
}

let load_opnctx filename =
  let pcode = load_raw_code_from_file filename in
  let opnctx = StructureRaw.mk_normal_top_ctx pcode in
  let opnctx = List.map ~f:(fun (x, ty) -> (Op.force_id_to_op x, ty)) opnctx in
  opnctx

let load_opeffnctx filename =
  let ctx = load_opnctx filename in
  List.map
    ~f:(fun (op, t) ->
      let op' = match op with Op.BuiltinOp name -> Op.EffOp name | _ -> op in
      (op', t))
    ctx

let load_source_code { automata_preds; _ } source_codes =
  let code = List.concat @@ List.map ~f:load_raw_code_from_file source_codes in
  let code =
    StructureRaw.ltlf_to_srl @@ StructureRaw.inline_ltlf_pred @@ automata_preds
    @ code
  in
  code

let load_rctx s files =
  let code = load_source_code s files in
  let code = Ntypecheck.opt_to_typed_structure s.opnctx [] code in
  RTypectx.from_code code

let load_oppurerctx inputs_setting filename =
  ROpTypectx.to_opctx @@ load_rctx inputs_setting filename

let load_opeffrctx inputs_setting filename =
  ROpTypectx.to_effopctx @@ load_rctx inputs_setting filename

(* let load_rctx_and_nctx inputs_setting filename = *)
(*   let rctx = load_rctx inputs_setting filename in *)
(*   (List.map ~f:(fun (x, rty) -> (x, Rty.erase_rty rty)) rctx, rctx) *)

let pprint_setting { opnctx; automata_preds; oprctx; nctx; rctx } =
  (* Env.show_debug_preprocess @@ fun _ -> *)
  Printf.printf "\nTop Operation Normal Type Context:\n";
  NOpTypectx.pretty_print_lines opnctx;
  Printf.printf "\nTop Function Normal Type Context:\n";
  NTypectx.pretty_print_lines nctx;
  Printf.printf "\nAutomata Predicates:\n";
  List.iter
    ~f:(fun entry -> Printf.printf "%s\n" (StructureRaw.layout_entry entry))
    automata_preds;
  Printf.printf "\nTop Operation Rty Context:\n";
  ROpTypectx.pretty_print_lines oprctx;
  Printf.printf "\nTop Function Rty Context:\n";
  RTypectx.pretty_print_lines rctx

let init_setting
    {
      oppurenctx_files;
      opeffnctx_files;
      automata_pred_files;
      oppurerctx_files;
      opeffrctx_files;
      rctx_files;
      _;
    } =
  let opnctx1 = List.concat @@ List.map ~f:load_opnctx oppurenctx_files in
  let opnctx2 = List.concat @@ List.map ~f:load_opeffnctx opeffnctx_files in
  let opnctx = opnctx1 @ opnctx2 in
  let automata_preds =
    List.concat @@ List.map ~f:load_raw_code_from_file automata_pred_files
  in
  let setting = { opnctx; automata_preds; oprctx = []; nctx = []; rctx = [] } in
  (* let () = pprint_setting setting in *)
  (* let () = failwith "end" in *)
  let oprctx1 = load_oppurerctx setting oppurerctx_files in
  let oprctx2 = load_opeffrctx setting opeffrctx_files in
  let oprctx = oprctx1 @ oprctx2 in
  let rctx = load_rctx setting rctx_files in
  let nctx = List.map ~f:(fun (x, rty) -> (x, Rty.erase_rty rty)) rctx in
  let axs = load_axioms_from_file setting.opnctx @@ Env.get_axioms () in
  let () = Rty.Ax.init_builtin_axs axs in
  { setting with oprctx; nctx; rctx }

let print_source_code_ inputs_setting source_files =
  let setting = init_setting inputs_setting in
  let code = load_source_code setting source_files in
  let setting =
    { setting with nctx = setting.nctx @ StructureRaw.mk_normal_top_ctx code }
  in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    pprint_setting setting;
    Printf.printf "\nSource Code:\n";
    Printf.printf "\n%s\n" @@ StructureRaw.layout_structure code
  in
  (setting, code)

let ntyped_ (setting, code) =
  let code =
    Ntypecheck.opt_to_typed_structure setting.opnctx setting.nctx code
  in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "\nBasic Typed:\n";
    Printf.printf "%s\n" @@ Structure.layout_structure code
  in
  (setting, code)

let normalized_ (setting, code) =
  let normalized = Normalize.get_normalized_code code in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "\nNormalized:\n";
    List.iter
      ~f:(fun (name, e) ->
        Pp.printf "%s:\n%s\n" name (Denormalize.layout_comp_omit_type e))
      normalized
  in
  (setting, code, normalized)

let type_check_ s source_file =
  let setting, code, normalized =
    normalized_ @@ ntyped_ @@ print_source_code_ s source_file
  in
  (* let () = *)
  (*   Printf.printf "\n>>>>Top Operation Rty Context:\n"; *)
  (*   ROpTypectx.pretty_print_lines setting.oprctx *)
  (* in *)
  let ress = Typecheck.check (setting.oprctx, setting.rctx) code normalized in
  let () =
    Env.show_log "result" @@ fun _ -> List.iter ~f:Typecheck.pprint_res_one ress
  in
  (* let () = Stat.dump default_stat_file ress in *)
  let () = Printf.printf "%s\n" @@ Smtquery.(layout_cache check_bool_cache) in
  ()

(* let ri_type_check_ source_dir method_name = *)
(*   let source_file = sprintf "%s/%s.ml" source_dir method_name in *)
(*   let ri_file = sprintf "%s/ri.ml" source_dir method_name in *)
(*   let normalop_file = sprintf "%s/lib.ml" source_dir method_name in *)
(*   let rop_file = sprintf "%s/lib_rty.ml" source_dir method_name in *)
(*   let oprctx, rctx, code, normalized = *)
(*     print_typed_normalized_source_code_ source_file *)
(*   in *)
(*   let ress = Typecheck.check (oprctx, rctx) code normalized in *)
(*   let () = *)
(*     Env.show_log "result" @@ fun _ -> List.iter ~f:Typecheck.pprint_res_one ress *)
(*   in *)
(*   (\* let () = Stat.dump default_stat_file ress in *\) *)
(*   let () = Printf.printf "%s\n" @@ Smtquery.(layout_cache check_bool_cache) in *)
(*   () *)

let subtype_check_ s source_file =
  let setting, code, normalized =
    normalized_ @@ ntyped_ @@ print_source_code_ s source_file
  in
  (* let opctx, rctx = ROpTypectx.from_code code in *)
  (* let opctx = opctx @ opctx' in *)
  (* let rctx = rctx @ setting.rctx in *)
  let assertions = RTypectx.get_task code in
  let get x =
    snd @@ List.find_exn ~f:(fun (name, _) -> String.equal x name) assertions
  in
  let rty1 = get "rty1" in
  let rty2 = get "rty2" in
  let res = Subtyping.sub_rty_bool [] (rty1, rty2) in
  let () =
    Printf.printf "subtyping check\n%s\n<:\n%s\nresult: %b\n"
      (Rty.layout_rty rty1) (Rty.layout_rty rty2) res
  in
  ()

let typecheck_cmds =
  [
    ( "print-source-code",
      cmd_config_source "print raw source code"
        (fun meta_config_file source_file () ->
          let s = mk_inputs_setting meta_config_file in
          let x = print_source_code_ s [ source_file ] in
          ()) );
    ( "print-typed-source-code",
      cmd_config_source "print typed source code"
        (fun meta_config_file source_file () ->
          let s = mk_inputs_setting meta_config_file in
          let x = ntyped_ @@ print_source_code_ s [ source_file ] in
          ()) );
    ( "print-typed-normalized-source-code",
      cmd_config_source "print typed normalized source code"
        (fun meta_config_file source_file () ->
          let s = mk_inputs_setting meta_config_file in
          let x =
            normalized_ @@ ntyped_ @@ print_source_code_ s [ source_file ]
          in
          ()) );
    ( "ri-type-check",
      cmd_config_ir_source "type check" (fun meta_config_file dir name () ->
          let s = mk_inputs_setting meta_config_file in
          let ri_file = sprintf "%s/ri.ml" dir in
          let pred_file = sprintf "%s/automata_preds.ml" dir in
          let source_file = sprintf "%s/%s.ml" dir name in
          let libntyfile = sprintf "%s/lib_nty.ml" dir in
          let librtyfile = sprintf "%s/lib_rty.ml" dir in
          let s =
            {
              s with
              automata_pred_files = s.automata_pred_files @ [ pred_file ];
              opeffnctx_files = s.opeffnctx_files @ [ libntyfile ];
              opeffrctx_files = s.opeffrctx_files @ [ librtyfile ];
            }
          in
          let x = type_check_ s [ ri_file; source_file ] in
          ()) );
    ( "type-check",
      cmd_config_source "type check" (fun meta_config_file source_file () ->
          let s = mk_inputs_setting meta_config_file in
          let x = type_check_ s [ source_file ] in
          ()) );
    ( "subtype-check",
      cmd_config_source "subtype check" (fun meta_config_file source_file () ->
          let s = mk_inputs_setting meta_config_file in
          let x = subtype_check_ s [ source_file ] in
          ()) );
  ]
