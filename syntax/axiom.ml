module F (L : Lit.T) = struct
  module Nt = Lit.Ty
  module P = Qualifier.F (L)
  include P

  type ax = { name : string; uninterops : string list; body : prop }

  let builtin_axs : ax list option ref = ref None
  let init_builtin_axs axs = builtin_axs := Some axs

  let mk_ax (name, body) =
    let uninterops = get_uninterops body in
    { name; uninterops; body }

  open Zzdatatype.Datatype

  let is_related_ax ops { uninterops; _ } =
    match List.interset String.equal uninterops ops with
    | [] -> false
    | _ -> true

  let get_related_axs ops axs = List.filter (is_related_ax ops) axs

  open Sugar

  let get_related_assumption ops =
    match !builtin_axs with
    | None -> _failatwith __FILE__ __LINE__ "die"
    | Some axs ->
        let axs = get_related_axs ops axs in
        let assumption = And (List.map (fun { body; _ } -> body) axs) in
        assumption
end
