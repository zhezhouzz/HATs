module type Predictable = sig
  type lit
  type prop

  val mk_true : prop
  val mk_false : prop
  val mk_lit : lit -> prop
  val mk_ite : lit -> prop -> prop -> prop
  val layout_lit : lit -> string
end

module F (P : Predictable) = struct
  open P
  open FastDT
  open Sugar
  open Zzdatatype.Datatype

  type features = lit array
  type label = Pos | Neg | MayNeg
  type fvtab = (bool list, label) Hashtbl.t
  type t = T | F | Leaf of int | Node of int * t * t

  let layout_label = function Pos -> "pos" | Neg -> "neg" | MayNeg -> "mayneg"

  let eq_label a b =
    match (a, b) with
    | Pos, Pos | Neg, Neg | MayNeg, MayNeg -> true
    | _ -> false

  let init_fvtab features =
    let len = Array.length features in
    let init_fv = List.init len (fun _ -> false) in
    let rec next fv =
      match fv with
      | [] -> None
      | false :: fv -> Some (true :: fv)
      | true :: fv ->
          let* fv = next fv in
          Some (false :: fv)
    in
    let fvtab = Hashtbl.create (pow 2 (Array.length features)) in
    let rec loop fv =
      Hashtbl.add fvtab fv MayNeg;
      match next fv with None -> () | Some fv' -> loop fv'
    in
    let () = loop init_fv in
    fvtab

  let layout_raw_fv fv = List.split_by ";" (fun b -> spf "%b" b) fv

  let layout_fv features fv =
    let props =
      List.mapi
        (fun id b ->
          let lit = features.(id) in
          spf "%s:%b" (layout_lit lit) b)
        fv
    in
    List.split_by "; " (fun x -> x) props

  let pprint_fvtab features fvtab =
    Hashtbl.iter
      (fun fv label ->
        Printf.printf "[%s] %s\n" (layout_label label) (layout_fv features fv))
      fvtab

  (* let rec layout = function *)
  (*   | T -> "⊤" *)
  (*   | F -> "⊥" *)
  (*   | Leaf feature -> F.layout feature *)
  (*   | Node (feature, l, r) -> *)
  (*       sprintf "[%s](%s,%s)" (F.layout feature) (layout l) (layout r) *)

  let pick_by_label fvtab lab =
    Hashtbl.fold
      (fun fv label res ->
        match res with
        | None -> if eq_label label lab then Some fv else None
        | Some fv -> Some fv)
      fvtab None

  let label_as fvtab fv label = Hashtbl.replace fvtab fv label

  let of_fastdt dt =
    let rec aux = function
      | FastDT.Leaf { c_t; c_f } ->
          let res =
            if Float.abs c_t < 1e-3 then F
            else if Float.abs c_f < 1e-3 then T
            else
              _failatwith __FILE__ __LINE__
                (spf "Bad Dt Result(%f, %f)" c_t c_f)
          in
          res
      | FastDT.Node { split; if_t; if_f } -> Node (split, aux if_t, aux if_f)
    in
    aux dt

  let to_prop (features : lit array) (dt : t) =
    let rec aux dt =
      match dt with
      | T -> mk_true
      | F -> mk_false
      | Leaf id -> mk_lit (Array.get features id)
      | Node (id, dt_l, dt_r) ->
          let dt_l, dt_r = map2 aux (dt_l, dt_r) in
          mk_ite (Array.get features id) dt_l dt_r
    in
    aux dt

  let classify_hash (len : int) (htab : fvtab) (is_pos : label -> bool) =
    let samples =
      Array.init (pow 2 len) (fun _ -> (false, Array.init len (fun _ -> false)))
    in
    let iter = ref 0 in
    let _ =
      Hashtbl.iter
        (fun f v ->
          Array.set samples !iter (is_pos v, Array.of_list f);
          iter := !iter + 1)
        htab
    in
    let () =
      Array.iter
        (fun (tf, barr) ->
          Printf.printf "%b: %s\n" tf
            (List.split_by ";" (fun x -> if x then "T" else "F")
            @@ Array.to_list barr))
        samples
    in
    let dt = FastDT.make_dt ~samples ~max_d:500 in
    of_fastdt dt

  let is_not_neg = function Neg -> false | _ -> true

  (* let classify_hash (features : lit array) (htab : fvtab) f = *)
  (*   let len = Array.length features in *)
  (*   let res = classify_hash_ len htab f in *)
  (*   res *)

  let classify_hash_is_not_neg len (htab : fvtab) =
    classify_hash len htab is_not_neg

  let predicate (dt : t) (fv : bool array) =
    let rec aux dt =
      match dt with
      | T -> true
      | F -> false
      | Leaf id -> Array.get fv id
      | Node (id, l, r) -> if Array.get fv id then aux l else aux r
    in
    aux dt
end
