exception FailWithModel of string * Z3.Model.model

let _failwithmodel file line msg model =
  raise (FailWithModel (Printf.sprintf "[%s:%i] %s" file line msg, model))

let ctx =
  Z3.mk_context [ ("model", "true"); ("proof", "false"); ("timeout", "99999") ]

exception SMTTIMEOUT

let _check pre q =
  let open Check in
  let time_t, res = Sugar.clock (fun () -> Check.smt_neg_and_solve ctx pre q) in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Pp.printf "@{<bold>Solving time: %.2f@}\n" time_t
  in
  match res with
  | SmtUnsat -> None
  | SmtSat model ->
      ( Env.show_debug_stat @@ fun _ ->
        Printf.printf "model:\n%s\n"
        @@ Sugar.short_str 100 @@ Z3.Model.to_string model );
      Some model
  | Timeout -> raise SMTTIMEOUT

let check_with_pre pres vc = _check pres vc

let check_implies_with_pre pres a b =
  _check pres Language.Rty.P.(Implies (a, b))

let check vc = check_with_pre [] vc
let check_implies a b = check_implies_with_pre [] a b
