module type Predictable = sig
  type lit
  type prop

  val mk_true : prop
  val mk_false : prop
  val mk_lit : lit -> prop
  val mk_ite : lit -> prop -> prop -> prop
  val mk_and : lit -> prop -> prop
  val mk_not_lit_and : lit -> prop -> prop
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
  type t = T | F | Node of int * t * t

  let layout_label = function Pos -> "pos" | Neg -> "neg" | MayNeg -> "mayneg"

  let refine_dt_under_prop (sat_checker : prop -> bool) prop (features, dt) =
    let counter = ref 0 in
    let sat_checker prop =
      counter := !counter + 1;
      sat_checker prop
    in
    let rec aux prop dt =
      if not (sat_checker prop) then F
      else
        match dt with
        | T -> T
        | F -> F
        | Node (idx, dt_t, dt_f) ->
            let lit = features.(idx) in
            let prop_t = mk_and lit prop in
            let prop_f = mk_not_lit_and lit prop in
            Node (idx, aux prop_t dt_t, aux prop_f dt_f)
    in
    let res = aux prop dt in
    (!counter, res)

  let mk_complete_dt features =
    let rec aux idx =
      if idx >= Array.length features then T
      else Node (idx, aux (idx + 1), aux (idx + 1))
    in
    aux 0

  let dynamic_classify (sat_checker : prop -> bool) features =
    let dt = mk_complete_dt features in
    refine_dt_under_prop sat_checker mk_true (features, dt)

  let lits_to_tab l =
    let tab = Hashtbl.create (List.length l) in
    List.iter (fun (lit, b) -> Hashtbl.add tab lit b) l;
    tab

  let dt_to_tab (features, dt) =
    let rec aux prefix dt =
      match dt with
      | T -> [ prefix ]
      | F -> []
      | Node (idx, dt_t, dt_f) ->
          let lit = features.(idx) in
          aux ((lit, true) :: prefix) dt_t @ aux ((lit, false) :: prefix) dt_f
    in
    let res = aux [] dt in
    let res = List.mapi (fun idx x -> (idx, lits_to_tab x)) res in
    res

  (* let dt_to_tab (features, dt) = *)
  (*   let rec aux prop dt = *)
  (*     match dt with *)
  (*     | T -> [ prop ] *)
  (*     | F -> [] *)
  (*     | Node (idx, dt_t, dt_f) -> *)
  (*         let lit = features.(idx) in *)
  (*         aux (mk_and lit prop) dt_t @ aux (mk_not_lit_and lit prop) dt_f *)
  (*   in *)
  (*   let res = aux  dt in *)
  (*   let res = List.mapi (fun idx x -> (idx, lits_to_tab x)) res in *)
  (*   res *)

  (* let rec lift_dt (n : int) dt = *)
  (*   match dt with *)
  (*   | T -> T *)
  (*   | F -> F *)
  (*   | Node (idx, dt_t, dt_f) -> Node (idx + n, lift_dt n dt_t, lift_dt n dt_f) *)

  (* let merge (sat_checker : prop -> bool) (feature1, dt1) (feature2, dt2) = *)
  (*   let features = Array.concat [ feature1; feature2 ] in *)
  (*   let dt2 = lift_dt (Array.length feature1) dt2 in *)
  (*   let rec aux prop dt1 = *)
  (*     match dt1 with *)
  (*     | F -> F *)
  (*     | T -> refine_dt_under_prop sat_checker prop (feature, dt2) *)
  (*     | Node (idx, dt_t, dt_f) -> *)
  (*         let lit = features.(idx) in *)
  (*         let prop_t = mk_and lit prop in *)
  (*         let prop_f = mk_not_lit_and lit prop in *)
  (*         Node (idx, aux prop_t dt_t, aux prop_f dt_f) *)
  (*   in *)
  (*   (features, aux mk_true dt1) *)

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
      (* | Leaf id -> mk_lit (Array.get features id) *)
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
      (* | Leaf id -> Array.get fv id *)
      | Node (id, l, r) -> if Array.get fv id then aux l else aux r
    in
    aux dt
end
