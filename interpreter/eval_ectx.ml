open Sugar
open Zzdatatype.Datatype

module F = struct
  open Language.OptTypedCoreEff
  (* open Constant *)

  exception ReductionErr of string

  let reduction_err file line str =
    raise (ReductionErr (spf "[%s::%i] Reduction Error: %s" file line str))

  let safe_combine file line l1 l2 =
    if List.length l1 != List.length l2 then
      reduction_err file line
        (spf "cannot combine lists (%i <> %i)" (List.length l1) (List.length l2))
    else List.combine l1 l2

  type frame =
    | FHandler of ty * handler typed
    | FNormal of (comp typed -> comp typed)

  type ectx = frame list

  let ectx_push ectx e = e :: ectx
  let ectx_pop ectx = match ectx with [] -> None | e :: ectx -> Some (e, ectx)
  let layout_comp = layout_comp

  (* let layout_comp e =  *)
  (* Sexplib.Sexp.to_string @@ sexp_of_comp e.x *)
  let recover_frame e = function
    | FHandler (ty, handler) -> { x = CWithH { handler; handled_prog = e }; ty }
    | FNormal f -> f e

  let rec recover_ectx e ectx =
    match ectx with
    | [] -> e
    | frame :: ectx -> recover_ectx (recover_frame e frame) ectx

  let box = mk_noty (CVal (VVar "□"))
  let layout_frame frame = layout_comp (recover_frame box frame)
  let layout_ectx ectx = List.split_by ";\n" layout_frame ectx

  let mk_ectx (comp : comp typed) =
    let rec mk_ectx_aux (cframe : comp typed -> comp typed) (ectx : ectx)
        (comp : comp typed) : ectx * comp typed =
      match comp.x with
      | CVal _ -> (ectx, cframe comp)
      | CLetE { lhs; rhs; letbody } -> (
          match rhs.x with
          | CVal _ ->
              let cframe letbody =
                cframe { x = CLetE { lhs; rhs; letbody }; ty = comp.ty }
              in
              mk_ectx_aux cframe ectx letbody
          | _ ->
              let cframe rhs =
                cframe { x = CLetE { lhs; rhs; letbody }; ty = comp.ty }
              in
              mk_ectx_aux cframe ectx rhs)
      | CLetApp { lhs; rhsf; rhsarg; letbody } ->
          let cframe letbody =
            cframe { x = CLetApp { lhs; rhsf; rhsarg; letbody }; ty = comp.ty }
          in
          mk_ectx_aux cframe ectx letbody
      | CLetPerform { lhs; rhsop; rhsargs; letbody } ->
          let cframe letbody =
            cframe
              { x = CLetPerform { lhs; rhsop; rhsargs; letbody }; ty = comp.ty }
          in
          mk_ectx_aux cframe ectx letbody
      | CWithH { handler; handled_prog } ->
          let ectx = ectx_push ectx (FNormal cframe) in
          let ectx = ectx_push ectx (FHandler (comp.ty, handler)) in
          (* let () = Printf.printf "zz: %s\n" @@ layout_comp handled_prog in *)
          let cframe x = x in
          mk_ectx_aux cframe ectx handled_prog
    in
    let ectx, comp = mk_ectx_aux (fun x -> x) [] comp in
    let _ = Printf.printf "Evaluation Ctx:\n%s\n" @@ layout_ectx ectx in
    let _ = Printf.printf "Current Compuation:\n%s\n" @@ layout_comp comp in
    (ectx, comp)

  type reduction_rule = StLetE1 | StLetE2 | StLetApp | StLetPerform

  type beta_result =
    | BRValue of value typed
    | BRComp of comp typed
    | BREffCall of {
        rbop : string typed;
        rbargs : value typed list;
        rbk : value typed -> comp typed;
      }

  let layout_beta_result = function
    | BRValue v -> spf "[Value: %s]" @@ layout_value v
    | BRComp comp -> spf "[Comp: %s]" @@ layout_comp comp
    | BREffCall { rbop; rbargs; rbk } ->
        spf "[Call: %s(%s, [%s])]" rbop.x
          (layout_comp (to_comp (mk_lam box (rbk (to_v box)))))
          (List.split_by ";" layout_value rbargs)

  let rec do_subst_value (x, v) e : value typed =
    match e.x with
    | VVar y -> if String.equal x y then v else e
    | VConst _ | VOp _ -> e
    | VLam { lamarg; lambody } ->
        if String.equal lamarg.x x then e
        else
          {
            x = VLam { lamarg; lambody = do_subst_comp (x, v) lambody };
            ty = e.ty;
          }
    | VHd hd -> { x = VHd (do_subst_handler (x, v) hd); ty = e.ty }

  and do_subst_handler (x, v) hd =
    match hd.x with
    | { ret_case; handler_cases } ->
        {
          hd with
          x =
            {
              ret_case =
                (if String.equal ret_case.retarg.x x then ret_case
                else
                  {
                    ret_case with
                    retbody = do_subst_comp (x, v) ret_case.retbody;
                  });
              handler_cases =
                List.map
                  (fun case ->
                    if
                      String.equal case.effk.x x
                      || List.exists (fun y -> String.equal x y.x) case.effargs
                    then case
                    else { case with hbody = do_subst_comp (x, v) case.hbody })
                  handler_cases;
            };
        }

  and do_subst_comp (x, v) e : comp typed =
    let ex =
      match e.x with
      | CVal _ -> (to_comp @@ do_subst_value (x, v) @@ to_v e).x
      | CWithH { handler; handled_prog } ->
          CWithH
            {
              handler = do_subst_handler (x, v) handler;
              handled_prog = do_subst_comp (x, v) handled_prog;
            }
      | CLetE { lhs; rhs; letbody } ->
          let rhs = do_subst_comp (x, v) rhs in
          if String.equal lhs.x x then CLetE { lhs; rhs; letbody }
          else CLetE { lhs; rhs; letbody = do_subst_comp (x, v) letbody }
      | CLetApp { lhs; rhsf; rhsarg; letbody } ->
          let rhsf = do_subst_value (x, v) rhsf in
          let rhsarg = do_subst_value (x, v) rhsarg in
          if String.equal lhs.x x then CLetApp { lhs; rhsf; rhsarg; letbody }
          else
            CLetApp
              { lhs; rhsf; rhsarg; letbody = do_subst_comp (x, v) letbody }
      | CLetPerform { lhs; rhsop; rhsargs; letbody } ->
          let rhsargs = List.map (do_subst_value (x, v)) rhsargs in
          if String.equal lhs.x x then
            CLetPerform { lhs; rhsop; rhsargs; letbody }
          else
            CLetPerform
              { lhs; rhsop; rhsargs; letbody = do_subst_comp (x, v) letbody }
    in
    { x = ex; ty = e.ty }

  let do_subst (l : (string * value typed) list) (comp : comp typed) :
      comp typed =
    (* let () = *)
    (*   Printf.printf "subster list: [%s]\n" *)
    (*     (List.split_by "; " *)
    (*        (fun (x, v) -> spf "%s |--> %s" x (layout_value v)) *)
    (*        l) *)
    (* in *)
    (* let () = Printf.printf "subst %s\n" (layout_comp comp) in *)
    List.fold_right do_subst_comp l comp

  let beta_reduction (comp : comp typed) : beta_result =
    let rec aux comp =
      match comp.x with
      | CVal v -> BRValue { x = v; ty = comp.ty }
      | CWithH _ -> failwith "never happen"
      | CLetE { lhs; rhs; letbody } ->
          BRComp
            (match rhs.x with
            | CVal v -> do_subst [ (lhs.x, { x = v; ty = rhs.ty }) ] letbody
            | _ -> (
                match aux rhs with
                | BRComp rhs ->
                    { x = CLetE { lhs; rhs; letbody }; ty = comp.ty }
                | _ -> failwith "never happen"))
      | CLetApp { lhs; rhsf; rhsarg; letbody } ->
          BRComp
            (match rhsf.x with
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
            | _ -> failwith "never happen")
      | CLetPerform { lhs; rhsop; rhsargs; letbody } ->
          BREffCall
            {
              rbop = rhsop;
              rbargs = rhsargs;
              rbk = (fun v -> do_subst [ (lhs.x, v) ] letbody);
            }
    in
    let res = aux comp in
    let () =
      match res with
      | BRValue _ -> ()
      | BRComp _ ->
          Printf.printf "%s ~~>> %s\n" (layout_comp comp)
            (layout_beta_result res)
      | BREffCall _ ->
          Printf.printf "%s === %s\n" (layout_comp comp)
            (layout_beta_result res)
    in
    res

  let rec find_handler_case op = function
    | [] -> None
    | case :: l ->
        if String.equal op.x case.effop.x then Some case
        else find_handler_case op l

  let rec reduction (comp : comp typed) =
    let ectx, comp = mk_ectx comp in
    match beta_reduction comp with
    | BRComp comp -> BRComp (recover_ectx comp ectx)
    | BRValue v -> (
        match ectx_pop ectx with
        | None -> BRValue v
        | Some (FNormal f, ectx) ->
            reduction (recover_ectx (f (to_comp v)) ectx)
        | Some
            ( FHandler
                ( _,
                  ({ x = { ret_case = { retarg; retbody }; _ }; _ } as handler)
                ),
              ectx ) ->
            let res = do_subst [ (retarg.x, v) ] retbody in
            let _ =
              Printf.printf "%s ~~> %s\n"
                (layout_comp (mk_with (to_comp v) handler))
                (layout_beta_result (BRComp res))
            in
            let res = BRComp (recover_ectx res ectx) in
            res)
    | BREffCall { rbop; rbargs; rbk } as ecall ->
        let rec shift ectx (rbk : value typed -> comp typed) =
          match ectx_pop ectx with
          | None ->
              reduction_err __FILE__ __LINE__
                (spf "unhandled effect: %s" rbop.x)
          | Some (frame, ectx) -> (
              match frame with
              | FNormal _ -> shift ectx (fun v -> recover_frame (rbk v) frame)
              | FHandler (_, ({ x = { handler_cases; _ }; _ } as handler)) -> (
                  match find_handler_case rbop handler_cases with
                  | None -> shift ectx (fun v -> recover_frame (rbk v) frame)
                  | Some { effargs; effk; hbody; _ } ->
                      let kx = mk_tvar (Rename.unique "x") in
                      let k = mk_lam kx (mk_with (rbk (to_v kx)) handler) in
                      let res =
                        do_subst
                          (safe_combine __FILE__ __LINE__
                             (effk.x :: List.map (fun x -> x.x) effargs)
                             (k :: rbargs))
                          hbody
                      in
                      let _ =
                        Printf.printf "handle %s with %s ~~> %s\n"
                          (layout_beta_result ecall) (layout_handler handler)
                          (layout_beta_result (BRComp res))
                      in
                      let res = BRComp (recover_ectx res ectx) in
                      res))
        in
        shift ectx rbk

  let eval comp =
    let counter = ref 0 in
    let rec eloop comp =
      let () = counter := !counter + 1 in
      let () = Printf.printf "\n[step %i]\n%s\n" !counter (layout_comp comp) in
      match reduction comp with
      | BRComp comp' -> eloop comp'
      | BRValue v ->
          let () = Printf.printf "\n[end %i]\n%s\n" !counter (layout_value v) in
          v
      | _ -> failwith "never happen"
    in
    eloop comp

  let example_prog =
    let x = mk_tvar "x" in
    let y = mk_tvar "x" in
    let z = mk_tvar "z" in
    let k = mk_tvar "k" in
    let retbody = x in
    let hbody = mk_letapp y k x y in
    let mk_hd op = mk_single_handler op retbody hbody in
    (fun e -> mk_lete x e x)
    @@ mk_with
         ((fun e ->
            mk_lete y
              (mk_with (mk_perform y (mk_noty "put") [ x ] y) (mk_hd "put"))
              (mk_lete z (mk_with x (mk_hd "get")) e))
         @@ mk_with x (mk_hd "lock"))
         (mk_hd "unlock")
end
