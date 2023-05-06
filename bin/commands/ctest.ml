open Core
open Caux

type format = Raw | Typed | MonadicNormalForm

open Language

let init_builtinctx () =
  let qfile = Env.get_builtin_coverage_type () in
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:qfile in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  let topnctx = StructureRaw.mk_normal_top_ctx code in
  NOpTypectx.to_builtin topnctx

let print_source_code_ meta_config_file source_file =
  let () = Env.load_meta meta_config_file in
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:source_file in
  (* let msize = Env.get_max_printing_size () in *)
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  let topnctx = StructureRaw.mk_normal_top_ctx code in
  let topnopctx = StructureRaw.mk_normal_top_opctx code in
  let topnopctx = NOpTypectx.new_to_rights topnopctx @@ init_builtinctx () in
  let () =
    Printf.printf "Top Type Context:\n%s\n\n" @@ NTypectx.pretty_layout topnctx
  in
  let () =
    Printf.printf "Top Operation Type Context:\n%s\n\n"
    @@ NOpTypectx.pretty_layout topnopctx
  in
  let () = Printf.printf "%s\n" @@ StructureRaw.layout_structure code in
  (topnctx, topnopctx, code)

let print_typed_source_code_ meta_config_file source_file =
  let topnctx, topnopctx, code =
    print_source_code_ meta_config_file source_file
  in
  let code = Ntypecheck.opt_to_typed_structure topnopctx topnctx code in
  let () = Printf.printf "%s\n" @@ Structure.layout_structure code in
  (topnctx, topnopctx, code)

let print_typed_normalized_source_code_ meta_config_file source_file =
  let topnctx, topnopctx, code =
    print_typed_source_code_ meta_config_file source_file
  in
  let normalized = Normalize.get_normalized_code code in
  let () =
    List.iter
      ~f:(fun (name, e) ->
        Pp.printf "%s:\n%s\n" name (Denormalize.layout_comp e))
      normalized
  in
  (code, normalized)

let type_check_ meta_config_file source_file =
  let code, normalized =
    print_typed_normalized_source_code_ meta_config_file source_file
  in
  (* let () = Typecheck.Typeinfer.check code normalized in *)
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
    ]
