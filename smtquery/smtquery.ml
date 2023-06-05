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
  match check vc with
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
  match check_inclusion (r1, r2) with
  | None -> true
  (* | Some _ -> *)
  | Some mt_list ->
      (* ( Env.show_debug_queries @@ fun _ -> *)
      (*   Printf.printf "model:\n%s\n" (Z3.Model.to_string model) ); *)
      ( Env.show_debug_queries @@ fun _ ->
        Pp.printf "@{<orange>counterexample word of language inclusion:@} %s\n"
          (Check.layout_counterexample mt_list) );
      false

let check_inclusion_counterexample (r1, r2) =
  match check_inclusion (r1, r2) with
  | None -> None
  | Some mt_list ->
      ( Env.show_debug_queries @@ fun _ ->
        Pp.printf "@{<orange>counterexample word of language inclusion:@} %s\n"
          (Check.layout_counterexample mt_list) );
      Some mt_list

let stat_init = Check.stat_init
let stat_get_cur = Check.stat_get_cur

open Language.NRegex

(* let test0 () = *)
(*   let open Zzdatatype.Datatype in *)
(*   let m = StrMap.add "z" 3 StrMap.empty in *)
(*   let x = (StrMap.map (fun x -> x + 1) m, m) in *)

let test0 () =
  (* let r1 = Epslion in *)
  let r1 =
    Minterm
      {
        op = "Put";
        global_embedding = 1;
        ret_embedding = 1;
        local_embedding = 3;
      }
  in
  (* let r2 = Concat [ Epslion; r1 ] in *)
  let r2 =
    Language.Rty.(
      SeqA
        ( EventA (GuardEvent mk_false),
          EventA (EffEvent { op = "Put"; vs = []; phi = mk_true }) ))
  in
  let dctx, mts = Desymbolic.ctx_init r2 in
  let () =
    Printf.printf "%b"
      (check_inclusion_bool (r1, Desymbolic.desymbolic dctx mts r2))
  in
  ()
