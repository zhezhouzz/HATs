open Language
module PCtx = PTypectx
module POpCtx = POpTypectx
module R = Rty
module P = Rty.P
module ECtx = Eqctx
open Sugar

let check opctx' structure normalized_structure =
  (* let () = *)
  (*   Printf.printf "Structure:\n%s\n" @@ Structure.layout_structure structure *)
  (* in *)
  let opctx, rctx = POpCtx.from_code structure in
  let opctx = opctx @ opctx' in
  (* let eqctx = Eqctx.from_code structure in *)
  (* let () = Printf.printf "!!! %s\n" @@ Eqctx.layout_equations eqctx in *)
  (* let () = failwith "end" in *)
  let tasks = RTypectx.get_task structure in
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
            let () = Printf.printf "%s\n" @@ Nt.layout comp.P.ty in
            let () =
              if not (Nt.eq comp.P.ty (R.erase rty)) then
                let () =
                  Printf.printf
                    "The erased type of the refinement type mismacted the \
                     implementation:\n\
                     %s (rty) !=\n\
                     %s (imp)\n"
                    (Nt.layout (R.erase rty))
                    (Nt.layout comp.P.ty)
                in
                _failatwith __FILE__ __LINE__ "input error"
              else ()
            in
            (* let () = failwith "end" in *)
            let res = Bidirectional.comp_type_check { rctx; opctx } comp rty in
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