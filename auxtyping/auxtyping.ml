let common_sub_rty = Fmerge.common_sub_rty
let common_sub_pty = Fmerge.common_sub_pty
let common_sub_rtys = Fmerge.common_sub_rtys
let common_sup_ptys = Fmerge.common_sup_ptys
let common_sub_ptys = Fmerge.common_sub_ptys

(* open Sugar *)

(* let purify _ _ _ _ = _failatwith __FILE__ __LINE__ "die" *)
let branchize_regex regex = Branching.branchize_regex regex
let simp regex = Simp.simp regex
(* let decide_ret_pty = Decide_ret.decide_ret *)
(* let concat = Concat.concat *)
