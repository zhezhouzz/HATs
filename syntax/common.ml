let v_name = "v"
let ret_name = "Ret"

(* let guard_name = "Guard" *)
let v_ret_name = "vret"

open Sugar

let str_eq_to_bv y x = match x with Some x -> String.equal x y | None -> false
let vs_names n = List.init n (fun i -> spf "%s%i" v_name i)

open Ntopt

let vs_names_from_types tps =
  let n = List.length tps in
  let vs = vs_names n in
  List.map (fun (x, ty) -> { x; ty }) @@ _safe_combine __FILE__ __LINE__ vs tps
