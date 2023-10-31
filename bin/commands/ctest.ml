open Core
open Caux

type format = Raw | Typed | MonadicNormalForm

open Language

let load_raw_code_from_file qfile =
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:qfile in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  code

let load_builtin_opctx () =
  let pcode = load_raw_code_from_file @@ Env.get_builtin_normal_type () in
  let opnctx = StructureRaw.mk_normal_top_ctx pcode in
  let opnctx = List.map ~f:(fun (x, ty) -> (Op.force_id_to_op x, ty)) opnctx in
  opnctx

let load_code_from_file qfile =
  let preds =
    load_raw_code_from_file @@ Env.get_builtin_automata_pred_type ()
  in
  StructureRaw.ltlf_to_srl @@ StructureRaw.inline_ltlf_pred @@ preds
  @ load_raw_code_from_file qfile

let load_typed_rtys_from_file opnctx file =
  let code = load_code_from_file file in
  let code = Ntypecheck.opt_to_typed_structure opnctx [] code in
  RTypectx.from_code code

let select_effops_code opnctx code =
  List.filter
    ~f:(fun entry ->
      match entry with
      | StructureRaw.Rty { name; _ } ->
          List.exists opnctx ~f:(fun (op', _) ->
              let op = Op.EffOp (String.capitalize name) in
              (* let () = *)
              (*   Printf.printf "%s == %s : %b\n" (Op.to_string op) *)
              (*     (Op.to_string op') *)
              (*     Op.(eq op op') *)
              (* in *)
              Op.(eq op op'))
      | _ -> false)
    code

let load_erased_ntys_from_file code =
  let opnctx = NOpTypectx.to_builtin @@ StructureRaw.mk_normal_top_ctx code in
  opnctx

let init_builtinctx () =
  let opnctx = load_builtin_opctx () in
  (* let () = Printf.printf "opnctx: %i\n" (List.length opnctx) in *)
  (* let () = *)
  (*   List.iter *)
  (*     ~f:(fun (op, ty) -> *)
  (*       Printf.printf "%s:%s\n" (Op.to_string op) (Nt.layout ty)) *)
  (*     opnctx *)
  (* in *)
  let prtys =
    load_typed_rtys_from_file opnctx @@ Env.get_builtin_pure_type ()
  in
  let poprctx = ROpTypectx.to_opctx prtys in
  let ertys = load_typed_rtys_from_file opnctx @@ Env.get_builtin_eff_type () in
  let eoprctx = ROpTypectx.to_effopctx ertys in
  (poprctx @ eoprctx, opnctx)

let print_raw_rty_ meta_config_file source_file =
  let () = Env.load_meta meta_config_file in
  let code = load_raw_code_from_file source_file in
  let () =
    List.iter
      ~f:(fun entry -> Printf.printf "%s\n" (StructureRaw.layout_entry entry))
      code
  in
  ()

let print_raw_rty_to_srl_ meta_config_file source_file =
  let () = Env.load_meta meta_config_file in
  let code = load_raw_code_from_file source_file in
  let code = StructureRaw.ltlf_to_srl code in
  let () =
    List.iter
      ~f:(fun entry -> Printf.printf "%s\n" (StructureRaw.layout_entry entry))
      code
  in
  ()

let print_raw_rty_without_pred_ meta_config_file source_file =
  let () = Env.load_meta meta_config_file in
  let code = load_raw_code_from_file source_file in
  let preds =
    load_raw_code_from_file @@ Env.get_builtin_automata_pred_type ()
  in
  let code = StructureRaw.inline_ltlf_pred (preds @ code) in
  let () =
    List.iter
      ~f:(fun entry -> Printf.printf "%s\n" (StructureRaw.layout_entry entry))
      code
  in
  ()

let print_rty_ meta_config_file source_file =
  let () = Env.load_meta meta_config_file in
  let opnctx = load_builtin_opctx () in
  let code = load_code_from_file source_file in
  let code = StructureRaw.ltlf_to_srl code in
  (* let () = *)
  (*   List.iter *)
  (*     ~f:(fun entry -> Printf.printf "%s\n" (StructureRaw.layout_entry entry)) *)
  (*     code *)
  (* in *)
  let code = Ntypecheck.opt_to_typed_structure opnctx [] code in
  let () =
    List.iter
      ~f:(fun entry -> Printf.printf "%s\n" (Structure.layout_entry entry))
      code
  in
  ()

let print_source_code_ meta_config_file source_file =
  let () = Env.load_meta meta_config_file in
  let oprctx, opnctx = init_builtinctx () in
  let code = load_code_from_file source_file in
  (* let msize = Env.get_max_printing_size () in *)
  let nctx = StructureRaw.mk_normal_top_ctx code in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "Top Type Context:\n%s\n\n" @@ NTypectx.pretty_layout nctx
  in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "Top Operation Type Context:\n%s\n\n"
    @@ NOpTypectx.pretty_layout opnctx
  in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "Top Operation Ptype Context:\n%s\n\n"
    @@ ROpTypectx.pretty_layout oprctx
  in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "%s\n" @@ StructureRaw.layout_structure code
  in
  (oprctx, nctx, opnctx, code)

let print_typed_source_code_ meta_config_file source_file =
  let oprctx, nctx, opnctx, code =
    print_source_code_ meta_config_file source_file
  in
  let code = Ntypecheck.opt_to_typed_structure opnctx nctx code in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "%s\n" @@ Structure.layout_structure code
  in
  (oprctx, nctx, opnctx, code)

let print_typed_normalized_source_code_ meta_config_file source_file =
  let oprctx, nctx, opnctx, code =
    print_typed_source_code_ meta_config_file source_file
  in
  let normalized = Normalize.get_normalized_code code in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    List.iter
      ~f:(fun (name, e) ->
        Pp.printf "%s:\n%s\n" name (Denormalize.layout_comp_omit_type e))
      normalized
  in
  (oprctx, code, normalized)

let default_stat_file = ".stat.json"

let type_check_ meta_config_file source_file =
  let oprctx, code, normalized =
    print_typed_normalized_source_code_ meta_config_file source_file
  in
  let ress = Typecheck.check oprctx code normalized in
  (* let () = Stat.dump default_stat_file ress in *)
  let () = Printf.printf "%s\n" @@ Smtquery.(layout_cache check_bool_cache) in
  ()

let subtype_check_ meta_config_file source_file =
  let opctx', code, normalized =
    print_typed_normalized_source_code_ meta_config_file source_file
  in
  let opctx, rctx = ROpTypectx.from_code code in
  let opctx = opctx @ opctx' in
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

let cmd_config_source summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file) in
      f meta_config_file source_file)

let test =
  Command.group ~summary:"Poirot"
    [
      ( "print-rty",
        cmd_config_source "print rty" (fun meta_config_file source_file () ->
            let x = print_rty_ meta_config_file source_file in
            ()) );
      ( "print-raw-rty",
        cmd_config_source "print raw rty (before desugar LTLf into SRL)"
          (fun meta_config_file source_file () ->
            let x = print_raw_rty_ meta_config_file source_file in
            ()) );
      ( "print-raw-rty-to-srl",
        cmd_config_source "print raw rty (before desugar LTLf into SRL)"
          (fun meta_config_file source_file () ->
            let x = print_raw_rty_to_srl_ meta_config_file source_file in
            ()) );
      ( "print-raw-rty-without-pred",
        cmd_config_source "print raw rty (before desugar LTLf into SRL)"
          (fun meta_config_file source_file () ->
            let x = print_raw_rty_without_pred_ meta_config_file source_file in
            ()) );
      ( "print-source-code",
        cmd_config_source "print raw source code"
          (fun meta_config_file source_file () ->
            let x = print_source_code_ meta_config_file source_file in
            ()) );
      ( "print-typed-source-code",
        cmd_config_source "print typed source code"
          (fun meta_config_file source_file () ->
            let x = print_typed_source_code_ meta_config_file source_file in
            ()) );
      ( "print-typed-normalized-source-code",
        cmd_config_source "print typed normalized source code"
          (fun meta_config_file source_file () ->
            let x =
              print_typed_normalized_source_code_ meta_config_file source_file
            in
            ()) );
      ( "type-check",
        cmd_config_source "type check" (fun meta_config_file source_file () ->
            let x = type_check_ meta_config_file source_file in
            ()) );
      ( "subtype-check",
        cmd_config_source "subtype check"
          (fun meta_config_file source_file () ->
            let x = subtype_check_ meta_config_file source_file in
            ()) )
      (* ( "test-reg", *)
      (*   cmd_config_source "test reg" (fun meta_config_file _ () -> *)
      (*       let () = Env.load_meta meta_config_file in *)
      (*       Smtquery.test0 ()) ); *);
    ]
