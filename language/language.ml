open Corelang
module TypedCoreEff = F (Ty.Ty)

module OptTypedCoreEff = struct
  include F (Ty.OptTy)

  let mk_noty x = { x; ty = None }
  let mk_unit = { x = CVal (VConst Constant.Unit); ty = Some Ty.Ty.TyUnit }
  let mk_int i = { x = CVal (VConst (Constant.Int i)); ty = Some Ty.Ty.TyInt }
  let mk_tvar name : comp typed = mk_noty @@ CVal (VVar name)

  let to_v tvar =
    match tvar.x with
    | CVal x -> { x; ty = tvar.ty }
    | _ -> failwith __FUNCTION__

  let to_comp { x; ty } = { x = CVal x; ty }

  let tvar_to_tstr tvar =
    match (to_v tvar).x with
    | VVar x -> { x; ty = tvar.ty }
    | _ -> failwith __FUNCTION__

  let mk_lam x lambody = mk_noty @@ VLam { lamarg = tvar_to_tstr x; lambody }

  let mk_lete lhs rhs letbody =
    mk_noty @@ CLetE { lhs = tvar_to_tstr lhs; rhs; letbody }

  let mk_letapp lhs rhsf rhsarg letbody =
    mk_noty
    @@ CLetApp
         {
           lhs = tvar_to_tstr lhs;
           rhsf = to_v rhsf;
           rhsarg = to_v rhsarg;
           letbody;
         }

  let mk_perform lhs rhsop rhsargs letbody =
    mk_noty
    @@ CLetPerform
         {
           lhs = tvar_to_tstr lhs;
           rhsop;
           rhsargs = List.map to_v rhsargs;
           letbody;
         }

  let mk_with handled_prog handler = mk_noty @@ CWithH { handler; handled_prog }
  let mk_ret_case_x retbody = { retarg = mk_noty "x"; retbody }

  let mk_handler_case_kx effop hbody =
    {
      effop = mk_noty effop;
      effargs = [ mk_noty "x" ];
      effk = mk_noty "k";
      hbody;
    }

  let mk_single_handler effop retbody hbody =
    mk_noty
    @@ {
         ret_case = mk_ret_case_x retbody;
         handler_cases = [ mk_handler_case_kx effop hbody ];
       }

  let layout_typed f { x; _ } = f x

  open Sugar
  open Zzdatatype.Datatype

  let rec layout_value (v : value typed) : string =
    layout_typed
      (function
        | VVar name -> name
        | VConst const -> Constant.layout const
        | VOp name -> name
        | VLam { lamarg; lambody } ->
            spf "(fun %s -> %s)"
              (layout_typed (fun x -> x) lamarg)
              (layout_comp lambody)
        | VHd hd -> layout_handler hd)
      v

  and layout_handler hd =
    layout_typed
      (fun { ret_case; handler_cases } ->
        let ret_case_str =
          spf "retc: fun %s -> %s"
            (layout_typed (fun x -> x) ret_case.retarg)
            (layout_comp ret_case.retbody)
        in
        let handler_case_strs =
          List.map
            (fun case ->
              spf "%s: fun %s %s -> %s"
                (layout_typed (fun x -> x) case.effop)
                (layout_typed (fun x -> x) case.effk)
                (List.split_by " " (layout_typed (fun x -> x)) case.effargs)
                (layout_comp case.hbody))
            handler_cases
        in
        spf "{%s}"
          (List.split_by "; " (fun x -> x) (ret_case_str :: handler_case_strs)))
      hd

  and layout_comp (comp : comp typed) : string =
    layout_typed
      (fun (compx : comp) ->
        match compx with
        | CVal v -> layout_value { x = v; ty = comp.ty }
        | CLetE { lhs; rhs; letbody } ->
            spf "let %s = %s in %s"
              (layout_typed (fun x -> x) lhs)
              (layout_comp rhs) (layout_comp letbody)
        | CLetApp { lhs; rhsf; rhsarg; letbody } ->
            spf "let %s = %s %s in %s"
              (layout_typed (fun x -> x) lhs)
              (layout_value rhsf) (layout_value rhsarg) (layout_comp letbody)
        | CLetPerform { lhs; rhsop; rhsargs; letbody } ->
            spf "let %s = perform %s %s in %s"
              (layout_typed (fun x -> x) lhs)
              (layout_typed (fun x -> x) rhsop)
              (List.split_by " " layout_value rhsargs)
              (layout_comp letbody)
        | CWithH { handler; handled_prog } ->
            spf "(handle %s with %s)" (layout_comp handled_prog)
              (layout_handler handler))
      comp

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
end
