open Core
open Caux

type format = Raw | Typed | MonadicNormalForm

open Language

let load_code_from_file qfile =
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:qfile in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  code

let select_effops_code topnopctx code =
  List.filter
    ~f:(fun entry ->
      match entry with
      | StructureRaw.Rty { name; _ } ->
          List.exists topnopctx ~f:(fun (op', _) ->
              let op = Op.EffOp (String.capitalize name) in
              (* let () = *)
              (*   Printf.printf "%s == %s : %b\n" (Op.to_string op) *)
              (*     (Op.to_string op') *)
              (*     Op.(eq op op') *)
              (* in *)
              Op.(eq op op'))
      | _ -> false)
    code

let load_ptys_from_file topnopctx code =
  let code = Ntypecheck.opt_to_typed_structure topnopctx [] code in
  let oprctx = POpTypectx.to_opctx @@ PTypectx.from_code code in
  oprctx

let load_erased_ntys_from_file code =
  let topnopctx =
    NOpTypectx.to_builtin @@ StructureRaw.mk_normal_top_ctx code
  in
  topnopctx

let init_builtinctx effopnctx =
  let pcode = load_code_from_file @@ Env.get_builtin_pure_type () in
  let topnopctx = load_erased_ntys_from_file pcode in
  let topnopctx = effopnctx @ topnopctx in
  (* let () = Printf.printf "%s\n" (NOpTypectx.layout_typed_l topnopctx) in *)
  (* let () = failwith "end" in *)
  let oprctx = load_ptys_from_file topnopctx pcode in
  let effcode = load_code_from_file @@ Env.get_builtin_eff_type () in
  let effcode = select_effops_code effopnctx effcode in
  let effcode = Ntypecheck.opt_to_typed_structure topnopctx [] effcode in
  let effoprctx = POpTypectx.to_effopctx @@ PTypectx.from_code effcode in
  (oprctx, effoprctx, topnopctx)

let print_source_code_ meta_config_file source_file =
  let () = Env.load_meta meta_config_file in
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:source_file in
  (* let msize = Env.get_max_printing_size () in *)
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  let topnctx = StructureRaw.mk_normal_top_ctx code in
  let effopnctx = StructureRaw.mk_normal_top_opctx code in
  let oprctx, effoprctx, opnctx = init_builtinctx effopnctx in
  let oprctx = POpTypectx.new_to_rights effoprctx @@ oprctx in
  let opnctx = effopnctx @ opnctx in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "Top Type Context:\n%s\n\n" @@ NTypectx.pretty_layout topnctx
  in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "Top Operation Type Context:\n%s\n\n"
    @@ NOpTypectx.pretty_layout opnctx
  in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "Top Operation Ptype Context:\n%s\n\n"
    @@ POpTypectx.pretty_layout oprctx
  in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "%s\n" @@ StructureRaw.layout_structure code
  in
  (oprctx, topnctx, opnctx, code)

let print_typed_source_code_ meta_config_file source_file =
  let oprctx, topnctx, topnopctx, code =
    print_source_code_ meta_config_file source_file
  in
  let code = Ntypecheck.opt_to_typed_structure topnopctx topnctx code in
  let () =
    Env.show_debug_preprocess @@ fun _ ->
    Printf.printf "%s\n" @@ Structure.layout_structure code
  in
  (oprctx, topnctx, topnopctx, code)

let print_typed_normalized_source_code_ meta_config_file source_file =
  let oprctx, topnctx, topnopctx, code =
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
  let () = Stat.dump default_stat_file ress in
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
      ( "test-reg",
        cmd_config_source "test reg" (fun meta_config_file _ () ->
            let () = Env.load_meta meta_config_file in
            Smtquery.test0 ()) );
    ]
