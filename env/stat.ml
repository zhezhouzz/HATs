open Yojson.Basic.Util

type interface_static_stat = {
  interface : string;
  numBranch : int;
  numVars : int;
}

let dump_interface_static_stat stat =
  `Assoc
    [
      ("interface", `String stat.interface);
      ("numBranch", `Int stat.numBranch);
      ("numVars", `Int stat.numVars);
    ]

let load_dt_static_stat j =
  {
    interface = j |> member "interface" |> to_string;
    numBranch = j |> member "numBranch" |> to_int;
    numVars = j |> member "numVars" |> to_int;
  }

type dt_static_stat = {
  dt : string;
  lib : string;
  numGhost : int;
  sizeRI : int;
  interfaceStatStatic : interface_static_stat list;
}

let dump_dt_static_stat stat =
  `Assoc
    [
      ("dt", `String stat.dt);
      ("lib", `String stat.lib);
      ("numGhost", `Int stat.numGhost);
      ("sizeRI", `Int stat.sizeRI);
      ( "interfaceStatStatic",
        `List (List.map dump_interface_static_stat stat.interfaceStatStatic) );
    ]

let load_dt_static_stat j =
  {
    dt = j |> member "dt" |> to_string;
    lib = j |> member "lib" |> to_string;
    numGhost = j |> member "numGhost" |> to_int;
    sizeRI = j |> member "sizeRI" |> to_int;
    interfaceStatStatic =
      j
      |> member "interfaceStatStatic"
      |> to_list
      |> List.map load_dt_static_stat;
  }

type inclusion_dynamic_stat = {
  sizeA : int;
  tTrans : float;
  tInclusion : float;
}

let dump_inclusion_dynamic_stat stat =
  `Assoc
    [
      ("sizeA", `Int stat.sizeA);
      ("tTrans", `Float stat.tTrans);
      ("tInclusion", `Float stat.tInclusion);
    ]

let load_inclusion_dynamic_stat j =
  {
    sizeA = j |> member "sizeA" |> to_int;
    tTrans = j |> member "tTrans" |> to_float;
    tInclusion = j |> member "tInclusion" |> to_float;
  }

type interface_dynamic_stat = {
  interfaceDynamic : string;
  numQuery : int;
  (* tInclusionPrepare : float; *)
  totalInclusionStat : inclusion_dynamic_stat list;
  tTypeCheck : float;
  result : bool;
}

let local_interface_dynamic_stat : interface_dynamic_stat ref =
  ref
    {
      interfaceDynamic = "";
      numQuery = 0;
      totalInclusionStat = [];
      tTypeCheck = 0.0;
      result = false;
    }

let init_interfaceDynamic interfaceDynamic =
  local_interface_dynamic_stat :=
    {
      interfaceDynamic;
      numQuery = 0;
      totalInclusionStat = [];
      tTypeCheck = 0.0;
      result = false;
    }

let appendInclusionStat stat =
  local_interface_dynamic_stat :=
    {
      !local_interface_dynamic_stat with
      totalInclusionStat =
        !local_interface_dynamic_stat.totalInclusionStat @ [ stat ];
    }

let numQueryPlus1 () =
  local_interface_dynamic_stat :=
    {
      !local_interface_dynamic_stat with
      numQuery = !local_interface_dynamic_stat.numQuery + 1;
    }

let settTypeCheck (result, tTypeCheck) =
  local_interface_dynamic_stat :=
    { !local_interface_dynamic_stat with tTypeCheck; result }

let dump_interface_dynamic_stat stat =
  `Assoc
    [
      ("interfaceDynamic", `String stat.interfaceDynamic);
      ("numQuery", `Int stat.numQuery);
      (* ("tInclusionPrepare", `Float stat.tInclusionPrepare); *)
      ( "totalInclusionStat",
        `List (List.map dump_inclusion_dynamic_stat stat.totalInclusionStat) );
      ("tTypeCheck", `Float stat.tTypeCheck);
      ("result", `Bool stat.result);
    ]

let load_interface_dynamic_stat j =
  {
    interfaceDynamic = j |> member "interfaceDynamic" |> to_string;
    numQuery = j |> member "numQuery" |> to_int;
    (* tInclusionPrepare = j |> member "tInclusionPrepare" |> to_float; *)
    tTypeCheck = j |> member "tTypeCheck" |> to_float;
    result = j |> member "result" |> to_bool;
    totalInclusionStat =
      j
      |> member "totalInclusionStat"
      |> to_list
      |> List.map load_inclusion_dynamic_stat;
  }

type dt_dynamic_stat = {
  dtDynamic : string;
  libDynamic : string;
  interfaceStatDynamic : interface_dynamic_stat list;
}

let dump_dt_dynamic_stat stat =
  `Assoc
    [
      ("dtDynamic", `String stat.dtDynamic);
      ("libDynamic", `String stat.libDynamic);
      ( "interfaceStatDynamic",
        `List (List.map dump_interface_dynamic_stat stat.interfaceStatDynamic)
      );
    ]

let load_dt_dynamic_stat j =
  (* let () = Printf.printf "??:%s\n" (j |> member "dtDynamic" |> to_string) in *)
  {
    dtDynamic = j |> member "dtDynamic" |> to_string;
    libDynamic = j |> member "libDynamic" |> to_string;
    interfaceStatDynamic =
      j
      |> member "interfaceStatDynamic"
      |> to_list
      |> List.map load_interface_dynamic_stat;
  }

let load_create statfile =
  let j =
    if Sys.file_exists statfile then Yojson.Basic.from_file statfile
    else
      let oc =
        Core.Out_channel.create ~binary:false ~append:false
          ~fail_if_exists:false ~perm:0o644 statfile
      in
      Core.Out_channel.close oc;
      `Assoc [ ("static", `List []); ("dynamic", `List []) ]
  in
  let static_stat =
    j |> member "static" |> to_list |> List.map load_dt_static_stat
  in
  let dynamic_stat =
    j |> member "dynamic" |> to_list |> List.map load_dt_dynamic_stat
  in
  (static_stat, dynamic_stat)

let save_stat statfile (static_stat, dynamic_stat) =
  let static_j = List.map dump_dt_static_stat static_stat in
  let dynamic_j = List.map dump_dt_dynamic_stat dynamic_stat in
  let j = `Assoc [ ("static", `List static_j); ("dynamic", `List dynamic_j) ] in
  Yojson.Basic.to_file statfile j

open Zzdatatype.Datatype

let merge_dt_static_interfaces a b =
  let la = a.interfaceStatStatic in
  let lb = b.interfaceStatStatic in
  let interfaceStatStatic =
    List.slow_rm_dup
      (fun a b ->
        (* Printf.printf "%s ?= %s\n" a.interface b.interface; *)
        String.equal a.interface b.interface)
      (la @ lb)
  in
  (* let () = *)
  (*   Printf.printf "len(interfaceStatStatic): %i\n" (List.length interfaceStatStatic) *)
  (* in *)
  { a with interfaceStatStatic }

let merge_dt_dynamic_interfaces a lb =
  let la = a.interfaceStatDynamic in
  let interfaceStatDynamic =
    List.slow_rm_dup
      (fun a b ->
        (* Printf.printf "%s ?= %s\n" a.interface b.interface; *)
        String.equal a.interfaceDynamic b.interfaceDynamic)
      (la @ lb)
  in
  (* let () = *)
  (*   Printf.printf "len(interfaceStatStatic): %i\n" (List.length interfaceStatStatic) *)
  (* in *)
  { a with interfaceStatDynamic }

(* open Sugar *)
let update_dt_static_stat (stat : dt_static_stat) =
  let statfile = Env.get_statfile () in
  let static_stat, dynamic_stat = load_create statfile in
  let old, rest =
    List.partition
      (fun one -> String.equal stat.dt one.dt && String.equal stat.lib one.lib)
      static_stat
  in
  (* let old = *)
  (*   match old with [ old ] -> old | _ -> _failatwith __FILE__ __LINE__ "die" *)
  (* in *)
  let stat =
    match old with [ old ] -> merge_dt_static_interfaces stat old | _ -> stat
  in
  let static_stat = stat :: rest in
  save_stat statfile (static_stat, dynamic_stat)

let update_dt_dynamic_stat (dt, lib, stat) =
  let statfile = Env.get_statfile () in
  let static_stat, dynamic_stat = load_create statfile in
  let old, rest =
    List.partition
      (fun one ->
        String.equal dt one.dtDynamic && String.equal lib one.libDynamic)
      dynamic_stat
  in
  let old =
    match old with
    | [ old ] -> old
    | _ -> { dtDynamic = dt; libDynamic = lib; interfaceStatDynamic = [] }
  in
  let stat = merge_dt_dynamic_interfaces old [ stat ] in
  let dynamic_stat = stat :: rest in
  save_stat statfile (static_stat, dynamic_stat)

(* let new_one = *)
(*   match old with *)
(*   | [] -> dump_dt_static_stat stat *)
(*   | [ old ] -> *)
(*       let interfaceStatDynamic_old = *)
(*         old |> member "interfaceStatDynamic" |> to_list *)
(*       in *)
(*       let interfaceStatDynamic_new = *)
(*         stat_j |> member "interfaceStatDynamic" |> to_list *)
(*       in *)
(*       let interfaceStatDynamic = *)
(*         List.interset *)
(*           (fun x y -> *)
(*             String.equal (x |> member "interface") (y |> member "interface")) *)
(*           interfaceStatDynamic_old interfaceStatDynamic_new *)
(*       in *)

(*       dump_dt_static_stat stat *)
(*   | _ -> _failatwith __FILE__ __LINE__ "die" *)
(* in *)
(* let static_j' = *)
(*   match old with *)
(*   | [] -> static_j @ [ dump_dt_static_stat stat ] *)
(*   | [ _ ] -> rest @ [ dump_dt_static_stat stat ] *)
(*   | _ -> _failatwith __FILE__ __LINE__ "die" *)
(* in *)
(* save_stat (static_stat, dynamic_stat) *)

(* let update_dt_static_stat (stat : dt_static_stat) = *)
(*   let statfile = Env.get_statfile () in *)
(*   let static_j, dynamic_j = load_create statfile in *)
(*   let old, rest = *)
(*     List.partition *)
(*       (fun one -> *)
(*         String.equal stat.dt (one |> member "dt" |> to_string) *)
(*         && String.equal stat.lib (one |> member "lib" |> to_string)) *)
(*       static_j *)
(*   in *)
(*   let static_j' = *)
(*     match old with *)
(*     | [] -> static_j @ [ dump_dt_static_stat stat ] *)
(*     | [ _ ] -> rest @ [ dump_dt_static_stat stat ] *)
(*     | _ -> _failatwith __FILE__ __LINE__ "die" *)
(*   in *)
(*   save_stat (static_j', dynamic_j) *)
