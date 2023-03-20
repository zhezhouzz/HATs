open Env

let load source_file =
  let prim_path = Env.get_prim_path () in
  let all_mps = Inputstage.load_user_defined_mps source_file in
  let () = init_known_mp all_mps in
  let measure = get_measure all_mps in
  let underp = Printf.sprintf "%s/%s.ml" prim_path.underp_dir measure in
  let rev_underp = Printf.sprintf "%s/%s.ml" prim_path.rev_underp_dir measure in
  let open Abstraction in
  let under_basicr =
    match Inputstage.load_under_refinments prim_path.under_basicp with
    | [], underr, [] -> underr
    | _, _, _ -> failwith "wrong under prim"
  in
  let underr =
    match Inputstage.load_under_refinments underp with
    | [], underr, [] -> underr
    | _, _, _ -> failwith "wrong under prim"
  in
  let underr =
    under_basicr @ underr
    (* __concat_without_overlap "basic underp is overlapped with underp" *)
    (*   (fun (x, _) (y, _) -> String.equal x y) *)
    (*   under_basicr underr *)
  in
  let rev_underr =
    let rtys =
      (* Inputstage.load_under_refinments rev_underp *)
      try Inputstage.load_under_refinments rev_underp with _ -> ([], [], [])
    in
    match rtys with
    | [], underr, [] -> underr
    | _, _, _ -> failwith "wrong under prim"
  in
  let lemmas = Inputstage.load_lemmas prim_path.lemmas in
  let lemmas =
    List.filter (fun (_, lemma) -> Lemma.filter_by_mps all_mps lemma) lemmas
  in
  let functional_lemmas = Inputstage.load_lemmas prim_path.functional_lemmas in
  let functional_lemmas =
    List.filter
      (fun (_, lemma) -> Lemma.filter_by_mps all_mps lemma)
      functional_lemmas
  in
  (* let () = failwith "end" in *)
  let () =
    Prim.init_refinement ([], underr, rev_underr, lemmas, functional_lemmas)
  in
  config := Some { all_mps; underp; measure }

let get_mps () =
  match !config with
  | None -> failwith "uninited prim path"
  | Some config -> config.all_mps
