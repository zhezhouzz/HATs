module type T = sig
  type constant = Constant.t [@@deriving sexp]

  include Typed.T

  type value =
    | VVar of string
    | VConst of constant
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VOp of string
    | VHd of handler typed

  and handler_case = {
    effop : string typed;
    effargs : string typed list;
    effk : string typed;
    hbody : comp typed;
  }

  and ret_case = { retarg : string typed; retbody : comp typed }
  and handler = { ret_case : ret_case; handler_cases : handler_case list }

  and comp =
    | CErr
    | CVal of value
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    | CLetApp of {
        lhs : string typed;
        rhsf : value typed;
        rhsarg : value typed;
        letbody : comp typed;
      }
    | CLetPerform of {
        lhs : string typed;
        rhsop : string typed;
        rhsargs : value typed list;
        letbody : comp typed;
      }
    | CWithH of { handler : handler typed; handled_prog : comp typed }
  [@@deriving sexp]

  val unit_ : comp
  val int_ : int -> comp
  val var_ : string -> comp
  val mk_unit : comp typed
  val mk_int : int -> comp typed
  val mk_bool : bool -> comp typed
  val mk_var : string -> comp typed
  val to_v_ : comp -> value
  val to_comp_ : value -> comp
  val to_v : comp typed -> value typed
  val to_comp : value typed -> comp typed
  val mk_lam : comp typed -> comp typed -> value typed
  val mk_lete : comp typed -> comp typed -> comp typed -> comp typed

  val mk_letapp :
    comp typed -> comp typed -> comp typed -> comp typed -> comp typed

  val mk_perform :
    comp typed -> string typed -> comp typed list -> comp typed -> comp typed

  val mk_with : comp typed -> handler typed -> comp typed
  val mk_ret_case_x : comp typed -> ret_case
  val mk_handler_case_kx : string -> comp typed -> handler_case
  val mk_single_handler : string -> comp typed -> comp typed -> handler typed
  val layout_value : value typed -> string
  val layout_handler : handler typed -> string
  val layout_comp : comp typed -> string
  val do_subst : (string * value typed) list -> comp typed -> comp typed
end

module F (Ty : Typed.T) : T with type t = Ty.t = struct
  open Sexplib.Std

  type constant = Constant.t [@@deriving sexp]

  include Ty

  type value =
    | VVar of string
    | VConst of constant
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VOp of string
    | VHd of handler typed

  and handler_case = {
    effop : string typed;
    effargs : string typed list;
    effk : string typed;
    hbody : comp typed;
  }

  and ret_case = { retarg : string typed; retbody : comp typed }
  and handler = { ret_case : ret_case; handler_cases : handler_case list }

  and comp =
    | CErr
    | CVal of value
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    | CLetApp of {
        lhs : string typed;
        rhsf : value typed;
        rhsarg : value typed;
        letbody : comp typed;
      }
    | CLetPerform of {
        lhs : string typed;
        rhsop : string typed;
        rhsargs : value typed list;
        letbody : comp typed;
      }
    | CWithH of { handler : handler typed; handled_prog : comp typed }
  [@@deriving sexp]

  let unit_ = CVal (VConst Constant.U)
  let int_ i = CVal (VConst (Constant.I i))
  let bool_ i = CVal (VConst (Constant.B i))
  let var_ name = CVal (VVar name)
  let mk_unit = unit_ #: unit_ty
  let mk_int i = (int_ i) #: int_ty
  let mk_bool i = (bool_ i) #: bool_ty
  let mk_var name : comp typed = mk_noty @@ var_ name

  open Sugar

  let to_v_ = function
    | CVal x -> x
    | _ -> _failatwith __FILE__ __LINE__ "not a value"

  let var_to_str_ = function
    | CVal (VVar x) -> x
    | _ -> _failatwith __FILE__ __LINE__ "not a var"

  let to_comp_ v = CVal v
  let to_v = xmap to_v_
  let to_comp = xmap to_comp_
  let var_to_str = xmap var_to_str_

  let mk_lam x lambody =
    (VLam { lamarg = var_to_str x; lambody }) #: (mk_arr x.ty lambody.ty)

  let mk_lete lhs rhs letbody =
    (CLetE { lhs = var_to_str lhs; rhs; letbody }) #: letbody.ty

  let mk_letapp lhs rhsf rhsarg letbody =
    (CLetApp
       { lhs = var_to_str lhs; rhsf = to_v rhsf; rhsarg = to_v rhsarg; letbody })
    #: letbody.ty

  let mk_perform lhs rhsop rhsargs letbody =
    (CLetPerform
       { lhs = var_to_str lhs; rhsop; rhsargs = List.map to_v rhsargs; letbody })
    #: letbody.ty

  let mk_with handled_prog handler =
    (CWithH { handler; handled_prog }) #: (get_retty handler.ty)

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
        | CErr -> "Err"
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
      | CErr -> CErr
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
