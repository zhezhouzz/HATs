open Sexplib.Std

type mode =
  | Debug of {
      show_preprocess : bool;
      show_typing : bool;
      show_queries : bool;
      show_solving : bool;
      show_stat : bool;
      show_info : bool;
      show_debug : bool;
    }
  | Release
[@@deriving sexp]

type prim_path = {
  qualifier_builtin_type : string;
  normalp : string;
  pure_p : string;
  eff_p : string;
  under_randomp : string;
  underp_dir : string;
  rev_underp_dir : string;
  type_decls : string;
  lemmas : string;
  functional_lemmas : string;
}
[@@deriving sexp]

type meta_config = {
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

let show_debug_preprocess (f : unit -> unit) =
  match get_mode () with
  | Debug { show_preprocess; _ } when show_preprocess -> f ()
  | _ -> ()

let show_debug_typing (f : unit -> unit) =
  match get_mode () with
  | Debug { show_typing; _ } when show_typing -> f ()
  | _ -> ()

let show_debug_queries (f : unit -> unit) =
  match get_mode () with
  | Debug { show_queries; _ } when show_queries -> f ()
  | _ -> ()

let show_debug_solving (f : unit -> unit) =
  match get_mode () with
  | Debug { show_solving; _ } when show_solving -> f ()
  | _ -> ()

let show_debug_stat (f : unit -> unit) =
  match get_mode () with
  | Debug { show_stat; _ } when show_stat -> f ()
  | _ -> ()

let show_debug_info (f : unit -> unit) =
  match get_mode () with
  | Debug { show_info; _ } when show_info -> f ()
  | _ -> ()

let show_debug_debug (f : unit -> unit) =
  match get_mode () with
  | Debug { show_debug; _ } when show_debug -> f ()
  | _ -> ()

let get_resfile () = (get_meta ()).resfile
let get_prim_path () = (get_meta ()).prim_path

let get_measure () =
  match !config with
  | None -> failwith "uninited prim path"
  | Some config -> config.measure

let get_randomp_path () = (get_prim_path ()).under_randomp
let get_qualifier_builtin_type () = (get_prim_path ()).qualifier_builtin_type
let get_builtin_pure_type () = (get_prim_path ()).pure_p
let get_builtin_eff_type () = (get_prim_path ()).eff_p
let known_mp : string list option ref = ref None

let get_known_mp () =
  match !known_mp with None -> failwith "uninit mps" | Some mps -> mps

open Yojson.Basic.Util

let load_meta meta_fname =
  (* let () = Printf.printf "meta_fname: %s\n" meta_fname in *)
  (* let () = Printf.printf "pwd: %s\n" (Sys.getcwd ()) in *)
  let metaj = Yojson.Basic.from_file meta_fname in
  let mode =
    match metaj |> member "mode" |> to_string with
    | "debug" ->
        (* let () = Pp.printf "@{<green>Verbose mode@}\n" in *)
        let get_bool field =
          metaj |> member "debug_info" |> member field |> to_bool
        in
        Debug
          {
            show_preprocess = get_bool "show_preprocess";
            show_typing = get_bool "show_typing";
            show_queries = get_bool "show_queries";
            (* we don't need this field *)
            show_solving = false;
            show_stat = get_bool "show_stat";
            show_info = get_bool "show_info";
            show_debug = (try get_bool "show_debug" with _ -> false);
          }
    | "release" -> Release
    | _ -> failwith "config: unknown mode"
  in
  let max_printing_size = metaj |> member "max_printing_size" |> to_int in
  let resfile = metaj |> member "resfile" |> to_string in
  let logfile = metaj |> member "logfile" |> to_string in
  let p = metaj |> member "prim_path" in
  let prim_path =
    {
      qualifier_builtin_type = p |> member "qualifier_builtin_type" |> to_string;
      normalp = p |> member "normal_typing" |> to_string;
      pure_p = p |> member "builtin_pure_typing" |> to_string;
      eff_p = p |> member "builtin_eff_typing" |> to_string;
      under_randomp =
        p |> member "builtin_randomness_coverage_typing" |> to_string;
      underp_dir = p |> member "builtin_datatype_coverage_typing" |> to_string;
      rev_underp_dir =
        p |> member "rev_builtin_datatype_coverage_typing" |> to_string;
      type_decls = p |> member "data_type_decls" |> to_string;
      lemmas = p |> member "axioms_of_predicates" |> to_string;
      functional_lemmas = p |> member "axioms_of_query_encoding" |> to_string;
    }
  in
  meta_config := Some { mode; max_printing_size; prim_path; logfile; resfile }
