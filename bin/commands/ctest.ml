open Core
open Caux

type format = Raw | Typed | MonadicNormalForm

open Language

let init_builtinctx () =
  let qfile = Env.get_builtin_coverage_type () in
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:qfile in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  let topnopctx =
    NOpTypectx.to_builtin @@ StructureRaw.mk_normal_top_ctx code
  in
  (* let () = Printf.printf "%s\n" (NOpTypectx.layout_typed_l topnopctx) in *)
  (* let () = failwith "end" in *)
  let code = Ntypecheck.opt_to_typed_structure topnopctx [] code in
  let oprctx = POpTypectx.to_opctx @@ PTypectx.from_code code in
  (oprctx, topnopctx)

let print_source_code_ meta_config_file source_file =
  let () = Env.load_meta meta_config_file in
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:source_file in
  (* let msize = Env.get_max_printing_size () in *)
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  let topnctx = StructureRaw.mk_normal_top_ctx code in
  let topnopctx = StructureRaw.mk_normal_top_opctx code in
  let oprctx, opnctx = init_builtinctx () in
  let topnopctx = NOpTypectx.new_to_rights topnopctx @@ opnctx in
  let () =
    Env.show_debug_typing @@ fun _ ->
    Printf.printf "Top Type Context:\n%s\n\n" @@ NTypectx.pretty_layout topnctx
  in
  let () =
    Env.show_debug_typing @@ fun _ ->
    Printf.printf "Top Operation Type Context:\n%s\n\n"
    @@ NOpTypectx.pretty_layout topnopctx
  in
  let () =
    Env.show_debug_typing @@ fun _ ->
    Printf.printf "%s\n" @@ StructureRaw.layout_structure code
  in
  (oprctx, topnctx, topnopctx, code)

let print_typed_source_code_ meta_config_file source_file =
  let oprctx, topnctx, topnopctx, code =
    print_source_code_ meta_config_file source_file
  in
  let code = Ntypecheck.opt_to_typed_structure topnopctx topnctx code in
  let () =
    Env.show_debug_typing @@ fun _ ->
    Printf.printf "%s\n" @@ Structure.layout_structure code
  in
  (oprctx, topnctx, topnopctx, code)

let print_typed_normalized_source_code_ meta_config_file source_file =
  let oprctx, topnctx, topnopctx, code =
    print_typed_source_code_ meta_config_file source_file
  in
  let normalized = Normalize.get_normalized_code code in
  let () =
    Env.show_debug_typing @@ fun _ ->
    List.iter
      ~f:(fun (name, e) ->
        Pp.printf "%s:\n%s\n" name (Denormalize.layout_comp e))
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
