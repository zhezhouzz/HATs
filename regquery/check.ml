open Z3
open Solver
open Goal
(* open Z3aux *)

type smt_result = SmtSat of Model.model | SmtUnsat | Timeout

let solver_result solver =
  (* let _ = printf "solver_result\n" in *)
  match check solver [] with
  | UNSATISFIABLE -> SmtUnsat
  | UNKNOWN ->
      (* raise (InterExn "time out!") *)
      (* Printf.printf "\ttimeout\n"; *)
      Timeout
  | SATISFIABLE -> (
      match Solver.get_model solver with
      | None -> failwith "never happen"
      | Some m -> SmtSat m)

let get_int m i =
  match Model.eval m i true with
  | None -> failwith "get_int"
  | Some v ->
      (* printf "get_int(%s)\n" (Expr.to_string i); *)
      int_of_string @@ Arithmetic.Integer.numeral_to_string v

let get_bool_str m i =
  match Model.eval m i true with None -> "none" | Some v -> Expr.to_string v

let get_int_name ctx m name =
  get_int m @@ Arithmetic.Integer.mk_const_s ctx name

let get_pred m predexpr =
  match Model.eval m predexpr true with
  | None -> failwith "get pred"
  | Some v -> Z3aux.z3expr_to_bool v

let get_unknown_fv ctx m unknown_fv =
  List.map (fun (_, b) -> get_pred m (Boolean.mk_const_s ctx b)) unknown_fv

(* let ctx = *)
(*   mk_context [ ("model", "true"); ("proof", "false"); ("timeout", "1999") ] *)

let smt_neg_and_solve ctx pre vc =
  (* let _ = printf "check\n" in *)
  let solver = mk_solver ctx None in
  let g = mk_goal ctx true false false in
  let () =
    Env.show_debug_query @@ fun _ ->
    Printf.printf "Q: %s\n" @@ Language.Rty.layout_prop vc
  in
  (* let () = Printf.printf "Q: %s\n" @@ Frontend.coq_layout vc in *)
  (* let () = failwith "zz" in *)
  let time_t, q =
    Sugar.clock (fun () -> Boolean.mk_not ctx @@ Propencoding.to_z3 ctx vc)
  in
  let () = Env.show_debug_stat @@ fun _ -> Pp.printf "to_Z3: %0.4fs\n" time_t in
  (* let () = exit 0 in *)
  let _ = Goal.add g (List.map (Propencoding.to_z3 ctx) pre @ [ q ]) in
  (* let g = Goal.simplify g None in *)
  (* let g = *)
  (*   Tactic.(ApplyResult.get_subgoal (apply (mk_tactic ctx "snf") g None) 0) *)
  (* in *)
  (* let () = *)
  (*   Printf.printf "Goal: %s\n\n" *)
  (*   @@ Zzdatatype.Datatype.List.split_by "\n" Expr.to_string *)
  (*   @@ Goal.get_formulas g *)
  (* in *)
  let _ = Solver.add solver (get_formulas g) in
  solver_result solver
