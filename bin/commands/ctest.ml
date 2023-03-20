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
  let topnctx = Structure.mk_normal_top_ctx code in
  (* let () = NTypectx.pretty_print topnctx in *)
  let () = Printf.printf "%s\n" @@ NTypectx.pretty_layout topnctx in
  let () = Printf.printf "%s\n" @@ To_structure.layout code in
  ()

let print_source_code =
  Command.basic ~summary:"print raw source code"
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file) in
      print_source_code_ meta_config_file source_file)

let test =
  Command.group ~summary:"Poirot" [ ("print-source-code ", print_source_code) ]
