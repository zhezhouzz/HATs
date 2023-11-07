open Core
open Caux
open Language

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

let test_cmds =
  [
    ( "print-rty",
      cmd_config_source "print rty" (fun meta_config_file source_file () ->
          let x = print_rty_ meta_config_file source_file in
          ()) );
    ( "print-raw",
      cmd_config_source "print raw (before desugar LTLf into SRL)"
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
  ]
