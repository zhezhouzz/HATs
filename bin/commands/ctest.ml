open Core
open Caux
open Frontend

type format = Raw | Typed | MonadicNormalForm

open Language

let print_source_code_ meta_config_file source_file () =
  let () = Env.load_meta meta_config_file in
  let code = Ocaml_parser.Frontend.parse ~sourcefile:source_file in
  let msize = Env.get_max_printing_size () in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  let topnctx = StructureRaw.mk_normal_top_ctx code in
  (* let () = NTypectx.pretty_print topnctx in *)
  let () =
    Printf.printf "Top Type Context:\n%s\n\n" @@ NTypectx.pretty_layout topnctx
  in
  let () = Printf.printf "%s\n" @@ StructureRaw.layout code in
  ()

let init_qnctx () =
  let qfile = Env.get_qualifier_builtin_type () in
  let code = Ocaml_parser.Frontend.parse ~sourcefile:qfile in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  let topnctx = StructureRaw.mk_normal_top_ctx code in
  topnctx

let print_typed_source_code_ meta_config_file source_file () =
  let () = Env.load_meta meta_config_file in
  let code = Ocaml_parser.Frontend.parse ~sourcefile:source_file in
  let msize = Env.get_max_printing_size () in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  let topnctx = StructureRaw.mk_normal_top_ctx code in
  let () = Printf.printf "%s\n" @@ StructureRaw.layout code in
  let effctx = NTypectx.get_effctx topnctx in
  let qctx = NTypectx.new_to_rights effctx (init_qnctx ()) in
  let code = Ntypecheck.struc_infer topnctx qctx code in
  let () = Printf.printf "%s\n" @@ Structure.layout code in
  ()

let print_typed_normalized_source_code_ meta_config_file source_file () =
  let () = Env.load_meta meta_config_file in
  let code = Ocaml_parser.Frontend.parse ~sourcefile:source_file in
  let msize = Env.get_max_printing_size () in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  let topnctx = StructureRaw.mk_normal_top_ctx code in
  let () = Printf.printf "%s\n" @@ StructureRaw.layout code in
  let effctx = NTypectx.get_effctx topnctx in
  let qctx = NTypectx.new_to_rights effctx (init_qnctx ()) in
  let code = Ntypecheck.struc_infer topnctx qctx code in
  let () = Printf.printf "%s\n" @@ Structure.layout code in
  let normalized = Normalize.get_normalized_code code in
  let () =
    List.iter
      ~f:(fun (name, e) ->
        Printf.printf "%s:\n%s\n" name (Denormalize.layout_comp e))
      normalized
  in
  let () = Typecheck.Typeinfer.check code normalized in
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
        cmd_config_source "print raw source code" print_source_code_ );
      ( "print-typed-source-code",
        cmd_config_source "print typed source code" print_typed_source_code_ );
      ( "print-typed-normalized-source-code",
        cmd_config_source "print typed normalized source code"
          print_typed_normalized_source_code_ );
    ]
