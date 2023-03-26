open Sugar
open Zzdatatype.Datatype

module F = struct
  open Ast.OptTypedCoreEff
  (* open Constant *)

  exception ReductionErr of string

  let reduction_err file line str =
    raise (ReductionErr (spf "[%s::%i] Reduction Error: %s" file line str))

  type rule =
    (* simulate the evaluation context *)
    | StLetERhs of rule
    | StWithHInner of rule
    | StLetEShift
    | StWithHShift
    (* other rules *)
    | StLetE
    | StWithHRet
    | StTu
    | StLetDeTu
    | StIteT
    | StIteF
    | StMatch
    | StApp
    | StAppOp
    | StPerform of (string typed * value typed list)

  let rec layout_rule = function
    | StLetERhs rule -> spf "StLetERhs %s" (layout_rule rule)
    | StWithHInner rule -> spf "StWithHInner %s" (layout_rule rule)
    | StLetEShift -> "StLetEShift"
    | StWithHShift -> "StWithHShift"
    | StLetE -> "StLetE"
    | StWithHRet -> "StWithHRet"
    | StTu -> "StTu"
    | StLetDeTu -> "StLetDeTu"
    | StIteT -> "StIteT"
    | StIteF -> "StIteF"
    | StMatch -> "StMatch"
    | StApp -> "StApp"
    | StAppOp -> "StAppOp"
    | StPerform (op, args) ->
        spf "StPerform %s (%s)" op.x (List.split_by_comma layout_value args)

  let layout_comp = layout_comp
  let box = mk_var "□"
  let layout_cont cont = layout_comp (cont box)

  type result = BRValue of value typed | BRComp of rule * comp typed

  let layout_result = function
    | BRValue v -> spf "[Value: %s]" @@ layout_value v
    | BRComp (rule, comp) ->
        spf " =={%s}==> [Comp: %s]" (layout_rule rule) (layout_comp comp)

  let rec find_handler_case op = function
    | [] -> None
    | case :: l ->
        if String.equal op.x case.effop.x then Some case
        else find_handler_case op l

  let rec find_match_case op = function
    | [] -> None
    | case :: l ->
        if Pmop.eq op case.constructor.x then Some case
        else find_match_case op l

  let rec reduction_withh handler handled_prog =
    match (handler.x, handled_prog.x) with
    | { ret_case = { retarg; retbody }; _ }, CVal _ ->
        BRComp (StWithHRet, do_subst_comp (retarg.x, to_v handled_prog) retbody)
    | { handler_cases; _ }, CAppPerform { effop; appopargs } -> (
        match find_handler_case effop handler_cases with
        | None -> BRComp (StWithHShift, handled_prog)
        | Some { effargs; effk; hbody; _ } ->
            let k = mk_id_function (get_retty effk.ty) in
            let res =
              do_multisubst_comp
                (_safe_combine __FILE__ __LINE__
                   (effk.x :: List.map (fun x -> x.x) effargs)
                   (k :: appopargs))
                hbody
            in
            BRComp (StPerform (effop, appopargs), res))
    | ( { handler_cases; _ },
        CLetE
          { lhs; rhs = { x = CAppPerform { effop; appopargs }; _ }; letbody } )
      -> (
        match find_handler_case effop handler_cases with
        | None ->
            let letbody =
              (CWithH { handler; handled_prog = letbody })
              #: (get_retty handler.ty)
            in
            BRComp (StWithHShift, mk_lete lhs handled_prog letbody)
        | Some { effargs; effk; hbody; _ } ->
            let k = mk_lam lhs letbody in
            let res =
              do_multisubst_comp
                (_safe_combine __FILE__ __LINE__
                   (effk.x :: List.map (fun x -> x.x) effargs)
                   (k :: appopargs))
                hbody
            in
            BRComp (StPerform (effop, appopargs), res))
    | _, _ -> (
        match reduction handled_prog with
        | BRComp (rule, handled_prog) ->
            BRComp
              ( StWithHInner rule,
                (CWithH { handler; handled_prog }) #: (get_retty handler.ty) )
        | _ -> failwith "never happen")

  and reduction_lete lhs rhs letbody =
    match rhs.x with
    | CVal v -> BRComp (StLetE, do_subst_comp (lhs.x, v #: rhs.ty) letbody)
    | _ -> (
        match reduction rhs with
        | BRComp (rule, rhs) -> BRComp (StLetERhs rule, mk_lete lhs rhs letbody)
        | _ -> failwith "never happen")

  and redunction_app appf apparg =
    match appf.x with
    | VLam { lamarg; lambody } ->
        BRComp (StApp, do_subst_comp (lamarg.x, apparg) lambody)
    | VFix { fixname; fixarg; fixbody } ->
        BRComp
          ( StApp,
            do_multisubst_comp [ (fixname.x, appf); (fixarg.x, apparg) ] fixbody
          )
    | _ -> failwith "wrong application"

  and reduction (comp : comp typed) : result =
    let get_const = function VConst c -> c | _ -> failwith "wrong const" in
    let res =
      match comp.x with
      | CErr -> failwith "end by CErr"
      | CVal v -> BRValue v #: comp.ty
      | CLetDeTu { tulhs; turhs; letbody } -> (
          match turhs.x with
          | VTu vs ->
              BRComp
                ( StLetDeTu,
                  do_multisubst_comp
                    (_safe_combine __FILE__ __LINE__
                       (List.map (fun x -> x.x) tulhs)
                       vs)
                    letbody )
          | _ -> failwith "wrong letdetu")
      | CIte { cond; et; ef } -> (
          match Constant.is_bool_opt (get_const cond.x) with
          | Some true -> BRComp (StIteT, et)
          | Some false -> BRComp (StIteT, ef)
          | None -> failwith "wrong ite")
      | CMatch { matched; match_cases } -> (
          match Constant.is_dt_opt (get_const matched.x) with
          | Some (op, vs) -> (
              match find_match_case op match_cases with
              | None -> failwith "wrong match case"
              | Some { args; exp; _ } ->
                  let vs =
                    List.map
                      (fun (x, c) -> (x.x, (VConst c) #: x.ty))
                      (_safe_combine __FILE__ __LINE__ args vs)
                  in
                  BRComp (StMatch, do_multisubst_comp vs exp))
          | None -> failwith "wrong match")
      | CLetE { lhs; rhs; letbody } -> reduction_lete lhs rhs letbody
      | CWithH { handler; handled_prog } -> reduction_withh handler handled_prog
      | CApp { appf; apparg } -> redunction_app appf apparg
      | CAppOp { op; appopargs } ->
          let cs = List.map (fun v -> get_const v.x) appopargs in
          let ty = snd @@ destruct_arr_tp op.ty in
          BRValue (VConst (Constant.mk_dt op.x cs)) #: ty
      | CAppPerform { effop; _ } ->
          reduction_err __FILE__ __LINE__
            (spf "unhandled effect call %s" effop.x)
    in
    let () =
      match res with
      | BRValue _ -> Printf.printf "End with %s\n" (layout_result res)
      | BRComp _ ->
          Printf.printf "%s %s\n" (layout_comp comp) (layout_result res)
    in
    res

  let eval comp =
    let counter = ref 0 in
    let rec eloop comp =
      let () = counter := !counter + 1 in
      let () = Printf.printf "\n[step %i]\n%s\n" !counter (layout_comp comp) in
      match reduction comp with
      | BRComp (_, comp') -> eloop comp'
      | BRValue v ->
          let () = Printf.printf "\n[end %i]\n%s\n" !counter (layout_value v) in
          v
    in
    eloop comp

  (* let example_prog = *)
  (*   let x = mk_var "x" in *)
  (*   let y = mk_var "x" in *)
  (*   let z = mk_var "z" in *)
  (*   let k = mk_var "k" in *)
  (*   let retbody = x in *)
  (*   let hbody = mk_letapp y k x y in *)
  (*   let mk_hd op = mk_single_handler op retbody hbody in *)
  (*   (fun e -> mk_lete x e x) *)
  (*   @@ mk_with *)
  (*        ((fun e -> *)
  (*           mk_lete y *)
  (*             (mk_with (mk_perform y (mk_noty "unlock") [ x ] y) (mk_hd "put")) *)
  (*             (mk_lete z (mk_with x (mk_hd "get")) e)) *)
  (*        @@ mk_with x (mk_hd "lock")) *)
  (*        (mk_hd "unlock") *)

  (* let put_get_prog = *)
  (*   let x = mk_var "x" in *)
  (*   let y = mk_var "x" in *)
  (*   let z = mk_var "z" in *)
  (*   let k = mk_var "k" in *)
  (*   let retbody = x in *)
  (*   let get_hd = mk_single_handler "get" retbody (mk_letapp y k (mk_int 3) y) in *)
  (*   let put_hd = mk_single_handler "put" retbody (mk_letapp y k mk_unit y) in *)
  (*   mk_with *)
  (*     (mk_with *)
  (*        (mk_perform x (mk_noty "put") *)
  (*           [ mk_int 3 ] *)
  (*           (mk_perform y (mk_noty "get") *)
  (*              [ mk_int 1 ] *)
  (*              (mk_perform z (mk_noty "put") [ mk_int 2 ] y))) *)
  (*        get_hd) *)
  (*     put_hd *)
end
