open Language
module RCtx = RTypectx
module R = Rty
module P = Rty.P
module ECtx = Eqctx
open Sugar

let check opctx' structure normalized_structure =
  (* let () = *)
  (*   Printf.printf "Structure:\n%s\n" @@ Structure.layout_structure structure *)
  (* in *)
  let opctx, rctx = RCtx.op_and_rctx_from_code structure in
  let opctx = opctx @ opctx' in
  let eqctx = Eqctx.from_code structure in
  (* let () = Printf.printf "!!! %s\n" @@ Eqctx.layout_equations eqctx in *)
  (* let () = failwith "end" in *)
  let tasks = RCtx.get_task structure in
  let ress =
    List.mapi
      (fun id (name, rty) ->
        let id = id + 1 in
        let () =
          Env.show_debug_typing @@ fun _ -> Pp.printf "@{<bold>Task %i:@}\n" id
        in
        match
          List.find_opt
            (fun (name', _) -> String.equal name name')
            normalized_structure
        with
        | None -> _failatwith __FILE__ __LINE__ ""
        | Some (_, comp) ->
            let res =
              Bidirectional.comp_type_check { rctx; opctx; eqctx } comp rty
            in
            let () =
              if res then
                Env.show_debug_typing @@ fun _ ->
                Pp.printf
                  "@{<bold>@{<yellow>Task %i, type check succeeded@}@}\n" id
              else
                Env.show_debug_typing @@ fun _ ->
                Pp.printf "@{<bold>@{<red>Task %i, type check failed@}@}\n" id
            in
            (id, res))
      tasks
  in
  ress
