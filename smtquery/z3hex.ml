type hexstr = string

open Sugar
open Zzdatatype.Datatype

let hex_offset = 16 * 16 * 16 * 16
let int_to_raw_hexstr i = Printf.sprintf "%X" (i + hex_offset)

let int_of_raw_hexstr i =
  let n = Scanf.sscanf i "%x" (fun x -> x) in
  n - hex_offset

let int_to_hexstr i = spf "\\u{%s}" @@ int_to_raw_hexstr i

let int_of_hexstr str =
  let len = String.length str in
  (* let () = Printf.printf "%s\n" str in *)
  let str = String.init (len - 4) @@ fun i -> String.get str (i + 3) in
  int_of_raw_hexstr str

let hex_range = 16 * 16 * 16 * 16

let intlist_of_hexstrs str =
  let cs = String.split_on_char '\\' str in
  let cs =
    List.filter_map
      (fun x -> match x with "" -> None | _ -> Some (spf "\\%s" x))
      cs
  in
  (* let () = Printf.printf "%s\n" @@ StrList.to_string cs in *)
  List.map int_of_hexstr cs
