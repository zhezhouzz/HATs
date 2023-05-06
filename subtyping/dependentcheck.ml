open Zzdatatype.Datatype
open Languages
open NL

type tt = Persistent | Resource
type ctx = tt StrMap.t

open Sugar

let consume_raw_ids (ctx : ctx) ids =
  List.fold_left
    (fun ctx id ->
      match StrMap.find_opt ctx id with
      | None -> failwith (spf "dependent syntax check: %s" id)
      | Some Resource -> StrMap.remove id ctx
      | Some Persistent -> ctx)
    ctx ids

let consume_ids (ctx : ctx) ids =
  consume_raw_ids ctx @@ List.map (fun x -> x.x) ids

let produce_raw_ids (ctx : ctx) ids =
  List.fold_left
    (fun ctx (id, tt) ->
      match StrMap.find_opt ctx id with
      | None ->
          (* let () = Printf.printf "@{<bold>Produce:@} %s\n" id in *)
          StrMap.add id tt ctx
      | Some _ ->
          _failatwith __FILE__ __LINE__
            (spf "dependent syntax check: duplicate variable %s" id))
    ctx ids

let produce_ids (ctx : ctx) ids =
  produce_raw_ids ctx
  @@ List.map
       (fun x ->
         (x.x, if NT.is_basic_tp (snd x.ty) then Resource else Persistent))
       ids

let merge ctxs =
  match ctxs with
  | [] -> failwith "never happen"
  | ctx :: ctxs ->
      StrMap.filter
        (fun name _ ->
          if
            List.for_all
              (fun ctx' ->
                StrMap.exists (fun name' _ -> String.equal name name') ctx')
              ctxs
          then true
          else false)
        ctx

let rec term_dependent_check (ctx : ctx) (term : term typed) : ctx =
  let rec aux ctx e =
    match e.x with
    | V v ->
        let ctx' = value_dependent_check ctx { x = v; ty = e.ty } in
        merge [ ctx; ctx' ]
    | LetTu { tu; args; body } ->
        let ctx = consume_ids ctx args in
        let ctx = produce_ids ctx [ tu ] in
        aux ctx body
    | LetDeTu { tu; args; body } ->
        let ctx = consume_ids ctx [ tu ] in
        let ctx = produce_ids ctx args in
        aux ctx body
    | LetOp { ret; body; _ } ->
        let ctx = produce_ids ctx [ ret ] in
        aux ctx body
    | LetApp { ret; args; body; _ } ->
        let ctx = consume_ids ctx args in
        let ctx = produce_ids ctx [ ret ] in
        aux ctx body
    | LetDtConstructor { ret; args; body; _ } ->
        let ctx = consume_ids ctx args in
        let ctx = produce_ids ctx [ ret ] in
        aux ctx body
    | LetVal { lhs; rhs; body } ->
        let ctx' = value_dependent_check ctx rhs in
        let ctx = merge [ ctx; ctx' ] in
        let ctx = produce_ids ctx [ lhs ] in
        aux ctx body
    | Ite { e_t; e_f; _ } -> merge (List.map (aux ctx) [ e_t; e_f ])
    | Match { cases; _ } ->
        let ctxs =
          List.map
            (fun { args; exp; _ } ->
              let ctx =
                produce_raw_ids ctx (List.map (fun x -> (x, Resource)) args)
              in
              aux ctx exp)
            cases
        in
        merge ctxs
  in
  aux ctx term

and value_dependent_check (ctx : ctx) (term : value typed) : ctx =
  let rec aux ctx e =
    match e.x with
    | Exn -> ctx
    | Lam (x, _, body) ->
        let ctx = produce_ids ctx [ x ] in
        term_dependent_check ctx body
    | Fix (f, body) ->
        let ctx = produce_ids ctx [ f ] in
        aux ctx body
    | Lit _ -> ctx
  in
  aux ctx term

let dependent_check funcs term =
  let ctx =
    produce_raw_ids StrMap.empty (List.map (fun x -> (x, Persistent)) funcs)
  in
  let _ = term_dependent_check ctx term in
  ()
