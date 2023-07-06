let common_sub_rty = Fmerge.common_sub_rty
let common_sub_pty = Fmerge.common_sub_pty
let common_sub_rtys = Fmerge.common_sub_rtys
let common_sup_ptys = Fmerge.common_sup_ptys
let common_sub_ptys = Fmerge.common_sub_ptys

(* open Sugar *)

(* let purify _ _ _ _ = _failatwith __FILE__ __LINE__ "die" *)
let branchize_regex regex =
  let runtime, res = Sugar.clock (fun () -> Branching.branchize_regex regex) in
  let () =
    Env.show_debug_debug @@ fun _ ->
    Pp.printf "@{<bold>branchize_regex: @}%f\n" runtime
  in
  res

let simp regex =
  let runtime, res = Sugar.clock (fun () -> Simp.simp regex) in
  let () =
    Env.show_debug_debug @@ fun _ -> Pp.printf "@{<bold>simp: @}%f\n" runtime
  in
  res
