open Autov.Prop
open Languages
open Ntyped

let u = { x = "u"; ty = Ty_int }
let w = { x = "w"; ty = Ty_int }
let mem = "mem"
let hd = "hd"
let len = "len"
let ord = "ord"
let make_iff f v1 v2 = Iff (f v1, f v2)
let make_mem u v = MethodPred (mem, [ AVar v; AVar u ])
let make_hd u v = MethodPred (hd, [ AVar v; AVar u ])
let make_len u v = MethodPred (len, [ AVar v; AVar u ])
let make_ord u w v = MethodPred (ord, [ AVar v; AVar u; AVar w ])
let make_eq_mem v1 v2 = Forall (u, make_iff (make_mem u) v1 v2)
let make_eq_hd v1 v2 = Forall (u, make_iff (make_hd u) v1 v2)
let make_eq_len v1 v2 = Forall (u, make_iff (make_len u) v1 v2)
let make_eq_ord v1 v2 = Forall (u, Forall (w, make_iff (make_ord u w) v1 v2))

let tab =
  [
    (mem, make_eq_mem); (hd, make_eq_hd); (len, make_eq_len); (ord, make_eq_ord);
  ]

open Sugar

let make_eq mps v1 v2 =
  let res =
    List.map
      (fun mp ->
        match List.find_opt (fun (x, _) -> String.equal x mp) tab with
        | None -> _failatwith __FILE__ __LINE__ ""
        | Some (_, f) -> f v1 v2)
      mps
  in
  And res

let make_eq_type mps x = UT.make_basic_from_prop x.ty (fun v -> make_eq mps v x)
