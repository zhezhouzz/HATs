open Sexplib.Std

type mode = DebugTags of string list | Release [@@deriving sexp]

type prim_path = {
  normal_p : string;
  pure_p : string;
  eff_p : string;
  libfunc_p : string;
  automata_pred_p : string;
  axioms_p : string;
  type_decls : string;
}
[@@deriving sexp]

type meta_config = {
  uninterops : string list;
  mode : mode;
  max_printing_size : int;
  logfile : string;
  resfile : string;
  prim_path : prim_path;
}
[@@deriving sexp]

type config = { all_mps : string list; underp : string; measure : string }
[@@deriving sexp]

let meta_config : meta_config option ref = ref None
let config : config option ref = ref None

let get_meta () =
  match !meta_config with None -> failwith "uninit" | Some config -> config

let get_mode () = (get_meta ()).mode
let get_max_printing_size () = (get_meta ()).max_printing_size

let show_log kw (f : unit -> unit) =
  match get_mode () with
  | DebugTags l when List.exists (String.equal kw) l -> f ()
  | _ -> ()

let show_debug_preprocess = show_log "preprocess"
let show_debug_typing = show_log "typing"
let show_debug_queries = show_log "queries"
let show_debug_minterms = show_log "minterms"
let show_debug_solving = show_log "solving"
let show_debug_stat = show_log "stat"
let show_debug_info = show_log "info"
let show_debug_debug = show_log "debug"
let get_resfile () = (get_meta ()).resfile
let get_prim_path () = (get_meta ()).prim_path
let get_uninterops () = (get_meta ()).uninterops

let get_measure () =
  match !config with
  | None -> failwith "uninited prim path"
  | Some config -> config.measure

let get_builtin_normal_type () = (get_prim_path ()).normal_p
let get_builtin_pure_type () = (get_prim_path ()).pure_p
let get_builtin_eff_type () = (get_prim_path ()).eff_p
let get_builtin_libfunc_type () = (get_prim_path ()).libfunc_p
let get_builtin_automata_pred_type () = (get_prim_path ()).automata_pred_p
let get_axioms () = (get_prim_path ()).axioms_p

open Yojson.Basic.Util

let load_meta meta_fname =
  (* let () = Printf.printf "meta_fname: %s\n" meta_fname in *)
  (* let () = Printf.printf "pwd: %s\n" (Sys.getcwd ()) in *)
  (* let () = Printf.printf "Loading meta-config.json...\n" in *)
  let () = Printf.printf "\n" in
  let metaj = Yojson.Basic.from_file meta_fname in
  let mode =
    match metaj |> member "mode" |> to_string with
    | "debug" ->
        (* let () = Pp.printf "@{<green>Verbose mode@}\n" in *)
        (* let get_bool field = *)
        (*   metaj |> member "debug_tags" |> member field |> to_bool *)
        (* in *)
        DebugTags (metaj |> member "debug_tags" |> to_list |> List.map to_string)
    | "release" -> Release
    | _ -> failwith "config: unknown mode"
  in
  let max_printing_size = metaj |> member "max_printing_size" |> to_int in
  let resfile = metaj |> member "resfile" |> to_string in
  let logfile = metaj |> member "logfile" |> to_string in
  let p = metaj |> member "prim_path" in
  let uninterops =
    metaj |> member "uninterops" |> to_list |> List.map to_string
  in
  let prim_path =
    {
      normal_p = p |> member "builtin_normal_typing" |> to_string;
      pure_p = p |> member "builtin_pure_typing" |> to_string;
      eff_p = p |> member "builtin_eff_typing" |> to_string;
      axioms_p = p |> member "builtin_axioms" |> to_string;
      libfunc_p = p |> member "builtin_libfunc_typing" |> to_string;
      automata_pred_p = p |> member "builtin_automata_pred_typing" |> to_string;
      type_decls = p |> member "data_type_decls" |> to_string;
    }
  in
  meta_config :=
    Some { mode; max_printing_size; prim_path; logfile; resfile; uninterops }
