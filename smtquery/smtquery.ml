exception FailWithModel of string * Z3.Model.model

let _failwithmodel file line msg model =
  raise (FailWithModel (Printf.sprintf "[%s:%i] %s" file line msg, model))

let ctx =
  Z3.mk_context
    [ ("model", "true"); ("proof", "false"); ("timeout", "9999999") ]

let _check pre q =
  Check.(handle_check_res (fun () -> smt_neg_and_solve ctx pre q))

let check_with_pre pres vc = _check pres vc

let check_implies_with_pre pres a b =
  _check pres Language.Rty.P.(Implies (a, b))

let check vc = check_with_pre [] vc

let check_bool vc =
  let runtime, res = Sugar.clock (fun () -> check vc) in
  let () =
    Env.show_debug_stat @@ fun _ -> Printf.printf "check_bool: %f\n" runtime
  in
  match res with
  | None -> true
  | Some _ ->
      (* | Some model -> *)
      (* ( Env.show_debug_queries @@ fun _ -> *)
      (*   Printf.printf "model:\n%s\n" (Z3.Model.to_string model) ); *)
      false

let check_implies a b = check_implies_with_pre [] a b

let check_implies_bool (a, b) =
  match check_implies a b with None -> true | Some _ -> false

let check_inclusion (r1, r2) = Check.inclusion_query ctx r1 r2

(* open Zzdatatype.Datatype *)

let check_inclusion_bool (r1, r2) =
  let runtime, res = Sugar.clock (fun () -> check_inclusion (r1, r2)) in
  let () =
    Env.show_debug_debug @@ fun _ ->
    Printf.printf "check_inclusion_bool: %f\n" runtime
  in
  match res with
  | None -> true
  (* | Some _ -> *)
  | Some mt_list ->
      (* ( Env.show_debug_queries @@ fun _ -> *)
      (*   Printf.printf "model:\n%s\n" (Z3.Model.to_string model) ); *)
      ( Env.show_debug_info @@ fun _ ->
        Pp.printf "@{<orange>counterexample word of language inclusion:@} %s\n"
          (Check.layout_counterexample mt_list) );
      false

let check_inclusion_counterexample (r1, r2) =
  let runtime, res = Sugar.clock (fun () -> check_inclusion (r1, r2)) in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Printf.printf "check_inclusion_counterexample: %f\n" runtime
  in
  match res with
  | None -> None
  | Some mt_list ->
      ( Env.show_debug_info @@ fun _ ->
        Pp.printf "@{<orange>counterexample word of language inclusion:@} %s\n"
          (Check.layout_counterexample mt_list) );
      Some mt_list

let stat_init = Check.stat_init
let stat_get_cur = Check.stat_get_cur
let test0 () = ()
