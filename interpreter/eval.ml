open Sugar
open Zzdatatype.Datatype

module F = struct
  open Ast.OptTypedCoreEff
  (* open Constant *)

  exception ReductionErr of string

  let reduction_err file line str =
    raise (ReductionErr (spf "[%s::%i] Reduction Error: %s" file line str))

  let safe_combine file line l1 l2 =
    if List.length l1 != List.length l2 then
      reduction_err file line
        (spf "cannot combine lists (%i <> %i)" (List.length l1) (List.length l2))
    else List.combine l1 l2

  type rule =
    | StLetERhs of rule
    | StLetEShift
    | StLetE
    | StLetApp
    | StHandleInner of rule
    | StHandleShift
    | StHandleRet
    | StHandlePerform of (string typed * value typed list)

  let rec layout_rule = function
    | StLetERhs rule -> spf "StLetERhs %s" (layout_rule rule)
    | StLetEShift -> "StLetEShift"
    | StLetE -> "StLetE"
    | StLetApp -> "StLetApp"
    | StHandleInner rule -> spf "StHandleInner %s" (layout_rule rule)
    | StHandleShift -> "StHandleShift"
    | StHandleRet -> "StHandleRet"
    | StHandlePerform (op, args) ->
        spf "StHandlePerform %s(%s)" op.x
          (List.split_by_comma layout_value args)

  let layout_comp = layout_comp
  let box = mk_noty (CVal (VVar "□"))
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

  let reduction (comp : comp typed) : result =
    let rec aux comp =
      let res =
        match comp.x with
        | CErr -> failwith "end by CErr"
        | CVal v -> BRValue { x = v; ty = comp.ty }
        | CWithH { handler; handled_prog } -> (
            match (handled_prog.x, handler.x) with
            | CVal _, { ret_case = { retarg; retbody }; _ } ->
                BRComp
                  ( StHandleRet,
                    do_subst [ (retarg.x, to_v handled_prog) ] retbody )
            | CLetPerform { lhs; rhsop; rhsargs; letbody }, { handler_cases; _ }
              -> (
                match find_handler_case rhsop handler_cases with
                | None ->
                    let res =
                      {
                        handled_prog with
                        x =
                          CLetPerform
                            {
                              lhs;
                              rhsop;
                              rhsargs;
                              letbody =
                                {
                                  x = CWithH { handler; handled_prog = letbody };
                                  ty = letbody.ty;
                                };
                            };
                      }
                    in
                    BRComp (StHandleShift, res)
                | Some { effargs; effk; hbody; _ } ->
                    let k =
                      mk_noty
                      @@ VLam
                           { lamarg = lhs; lambody = mk_with letbody handler }
                    in
                    let res =
                      do_subst
                        (safe_combine __FILE__ __LINE__
                           (effk.x :: List.map (fun x -> x.x) effargs)
                           (k :: rhsargs))
                        hbody
                    in
                    BRComp (StHandlePerform (rhsop, rhsargs), res))
            | _, _ -> (
                match aux handled_prog with
                | BRComp (rule, handled_prog) ->
                    BRComp
                      ( StHandleInner rule,
                        { comp with x = CWithH { handler; handled_prog } } )
                | _ -> failwith "never happen"))
        | CLetE { lhs; rhs; letbody } -> (
            match rhs.x with
            | CVal v ->
                BRComp
                  (StLetE, do_subst [ (lhs.x, { x = v; ty = rhs.ty }) ] letbody)
            | CLetPerform
                { lhs = lhs_inner; rhsop; rhsargs; letbody = letbody_inner } ->
                let res =
                  {
                    x =
                      CLetPerform
                        {
                          lhs = lhs_inner;
                          rhsop;
                          rhsargs;
                          letbody =
                            {
                              x = CLetE { lhs; rhs = letbody_inner; letbody };
                              ty = comp.ty;
                            };
                        };
                    ty = comp.ty;
                  }
                in
                BRComp (StLetEShift, res)
            | _ -> (
                match aux rhs with
                | BRComp (rule, rhs) ->
                    BRComp
                      ( StLetERhs rule,
                        { x = CLetE { lhs; rhs; letbody }; ty = comp.ty } )
                | _ -> failwith "never happen"))
        | CLetApp { lhs; rhsf; rhsarg; letbody } ->
            BRComp
              ( StLetApp,
                match rhsf.x with
                | VLam { lamarg; lambody } ->
                    {
                      x =
                        CLetE
                          {
                            lhs;
                            rhs = do_subst [ (lamarg.x, rhsarg) ] lambody;
                            letbody;
                          };
                      ty = comp.ty;
                    }
                | _ -> failwith "never happen" )
        | CLetPerform { rhsop; _ } ->
            reduction_err __FILE__ __LINE__
              (spf "unhandled effect call %s" rhsop.x)
      in
      let () =
        match res with
        | BRValue _ -> Printf.printf "End with %s\n" (layout_result res)
        | BRComp _ ->
            Printf.printf "%s %s\n" (layout_comp comp) (layout_result res)
      in
      res
    in
    let res = aux comp in
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

  let example_prog =
    let x = mk_var "x" in
    let y = mk_var "x" in
    let z = mk_var "z" in
    let k = mk_var "k" in
    let retbody = x in
    let hbody = mk_letapp y k x y in
    let mk_hd op = mk_single_handler op retbody hbody in
    (fun e -> mk_lete x e x)
    @@ mk_with
         ((fun e ->
            mk_lete y
              (mk_with (mk_perform y (mk_noty "unlock") [ x ] y) (mk_hd "put"))
              (mk_lete z (mk_with x (mk_hd "get")) e))
         @@ mk_with x (mk_hd "lock"))
         (mk_hd "unlock")

  let put_get_prog =
    let x = mk_var "x" in
    let y = mk_var "x" in
    let z = mk_var "z" in
    let k = mk_var "k" in
    let retbody = x in
    let get_hd = mk_single_handler "get" retbody (mk_letapp y k (mk_int 3) y) in
    let put_hd = mk_single_handler "put" retbody (mk_letapp y k mk_unit y) in
    mk_with
      (mk_with
         (mk_perform x (mk_noty "put")
            [ mk_int 3 ]
            (mk_perform y (mk_noty "get")
               [ mk_int 1 ]
               (mk_perform z (mk_noty "put") [ mk_int 2 ] y)))
         get_hd)
      put_hd
end
