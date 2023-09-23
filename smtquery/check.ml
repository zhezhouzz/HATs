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

let stat_smt_query_time_record = ref []
let stat_inclusion_query_time_record = ref []
let stat_inclusion_alphabet_record = ref []
let stat_inclusion_automaton_size_record = ref []
let stat_max_inclusion_alphabet = ref 0
let stat_max_inclusion_automaton_size = ref 0

let stat_init () =
  stat_smt_query_time_record := [];
  stat_inclusion_query_time_record := [];
  stat_inclusion_alphabet_record := [];
  stat_inclusion_automaton_size_record := [];
  stat_max_inclusion_alphabet := 0;
  stat_max_inclusion_automaton_size := 0

let stat_get_cur () =
  ( !stat_smt_query_time_record,
    !stat_inclusion_query_time_record,
    !stat_max_inclusion_alphabet,
    !stat_max_inclusion_automaton_size,
    !stat_inclusion_alphabet_record,
    !stat_inclusion_automaton_size_record )

let record_max record original n =
  record := !record @ [ n ];
  if n > !original then original := n else ()

let smt_solve ctx assertions =
  (* let _ = printf "check\n" in *)
  let solver = mk_solver ctx None in
  let g = mk_goal ctx true false false in
  (* let () = Printf.printf "Q: %s\n" @@ Frontend.coq_layout vc in *)
  (* let () = failwith "zz" in *)
  (* let () = exit 0 in *)
  let _ = Goal.add g assertions in
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
  let runtime, res = Sugar.clock (fun () -> solver_result solver) in
  let _ =
    stat_smt_query_time_record := !stat_smt_query_time_record @ [ runtime ]
  in
  res

let smt_neg_and_solve ctx pre vc =
  (* let () = *)
  (*   Env.show_debug_queries @@ fun _ -> *)
  (*   Printf.printf "Query: %s\n" @@ Language.Rty.layout_prop vc *)
  (* in *)
  let assertions =
    List.map (Propencoding.to_z3 ctx) (pre @ [ Language.Rty.Not vc ])
  in
  (* let () = *)
  (*   List.iter (fun q -> Printf.printf "SMT: %s\n" (Expr.to_string q)) assertions *)
  (* in *)
  let time_t, res = Sugar.clock (fun () -> smt_solve ctx assertions) in
  let () =
    Env.show_debug_stat @@ fun _ -> Pp.printf "Z3 solving time: %0.4fs\n" time_t
  in
  res

let sequence_name = "reg_query_string"

open Zzdatatype.Datatype
open Sugar

exception SMTTIMEOUT

let debug_counter = ref 0

let handle_check_res query_action =
  let time_t, res = Sugar.clock query_action in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Pp.printf "@{<bold>Solving time: %.2f@}\n" time_t
  in
  (* let () = *)
  (*   if 18 == !debug_counter then failwith "end" *)
  (*   else debug_counter := !debug_counter + 1 *)
  (* in *)
  match res with
  | SmtUnsat -> None
  | SmtSat model ->
      ( Env.show_debug_stat @@ fun _ ->
        Printf.printf "model:\n%s\n"
        @@ Sugar.short_str 100 @@ Z3.Model.to_string model );
      Some model
  | Timeout -> raise SMTTIMEOUT

let mk_q_version1 ctx r1 r2 =
  let encoding, r1, r2 = Regencoding.to_z3_two_reg ctx (r1, r2) in
  let sequence = Expr.mk_const_s ctx sequence_name (Seq.mk_string_sort ctx) in
  let q1 = Seq.mk_seq_in_re ctx sequence r1 in
  let q2 = Seq.mk_seq_in_re ctx sequence r2 in
  let () =
    Env.show_debug_queries @@ fun _ ->
    Printf.printf "Query:\n%s\n%s\n" (Expr.to_string q1) (Expr.to_string q2)
  in
  (encoding, [ q1; Boolean.mk_not ctx q2 ])

let mk_q_version2 ctx r1 r2 =
  let r12 = Language.NRegex.(Intersect [ r1; Complement r2 ]) in
  let encoding, r = Regencoding.to_z3_one_reg ctx r12 in
  let encoded_size = Regencoding.get_size encoding r12 in
  let sequence = Expr.mk_const_s ctx sequence_name (Seq.mk_string_sort ctx) in
  let q = Seq.mk_seq_in_re ctx sequence r in
  (* let () = *)
  (*   Env.show_debug_queries @@ fun _ -> *)
  (*   Printf.printf "R1:\n%s\n" *)
  (*     (Expr.to_string @@ Regencoding.to_z3 ctx encoding r1) *)
  (* in *)
  (* let () = *)
  (*   Env.show_debug_queries @@ fun _ -> *)
  (*   Printf.printf "R2:\n%s\n" *)
  (*     (Expr.to_string @@ Regencoding.to_z3 ctx encoding r2) *)
  (* in *)
  let () =
    Env.show_debug_info @@ fun _ ->
    Printf.printf "Query:\n%s\n" (Expr.to_string q)
  in
  (encoding, encoded_size, [ q ])

let layout_counterexample mt_list =
  match mt_list with
  | [] -> "ϵ"
  | _ -> List.split_by ";" Minterm.T.mt_to_string mt_list

let inclusion_query ctx r1 r2 =
  (* let open Sugar in *)
  let encoding, encoded_size, qs = mk_q_version2 ctx r1 r2 in
  let num_inclusion_alphabet = Regencoding.RegZ3.get_cardinal encoding in
  let _ =
    record_max stat_inclusion_alphabet_record stat_max_inclusion_alphabet
      num_inclusion_alphabet
  in
  let _ =
    record_max stat_inclusion_automaton_size_record
      stat_max_inclusion_automaton_size encoded_size
  in
  (* let () = *)
  (*   if 1 == !debug_counter then failwith "end" *)
  (*   else debug_counter := !debug_counter + 1 *)
  (* in *)
  let runtime, res =
    Sugar.clock (fun () -> handle_check_res (fun () -> smt_solve ctx qs))
  in
  let _ =
    stat_inclusion_query_time_record :=
      !stat_inclusion_query_time_record @ [ runtime ]
  in
  match res with
  | None ->
      ( Env.show_debug_queries @@ fun _ ->
        Pp.printf "@{<orange>inclusion is valid:@}\n" );
      (* let () = *)
      (*   if 1 == !debug_counter then failwith "end" *)
      (*   else debug_counter := !debug_counter + 1 *)
      (* in *)
      None
  | Some model ->
      (* let () = *)
      (*   if 1 == !debug_counter then failwith "end" *)
      (*   else debug_counter := !debug_counter + 1 *)
      (* in *)
      ( Env.show_debug_info @@ fun _ ->
        Printf.printf "model:\n%s\n" (Z3.Model.to_string model) );
      let str =
        match Z3aux.get_string_by_name model sequence_name with
        | Some str -> str
        | None -> _failatwith __FILE__ __LINE__ "die"
      in
      let mt_list = Regencoding.RegZ3.code_trace encoding str in
      (* ( Env.show_debug_queries @@ fun _ -> *)
      (*   Pp.printf "@{<orange>counterexample word of language inclusion:@} %s\n" *)
      (*     (layout_counterexample mt_list) ); *)
      (* let () = *)
      (*   if 1 == !debug_counter then failwith "end" *)
      (*   else debug_counter := !debug_counter + 1 *)
      (* in *)
      Some mt_list
