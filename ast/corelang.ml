module type T = sig
  type constant = Constant.t [@@deriving sexp]

  include Typed.T

  type value =
    | VVar of string
    | VConst of constant
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VFix of {
        fixname : string typed;
        fixarg : string typed;
        fixbody : comp typed;
      }
    | VTu of value typed list
    | VHd of handler typed

  and handler_case = {
    effop : string typed;
    effargs : string typed list;
    effk : string typed;
    hbody : comp typed;
  }

  and ret_case = { retarg : string typed; retbody : comp typed }
  and handler = { ret_case : ret_case; handler_cases : handler_case list }

  and match_case = {
    constructor : Pmop.t typed;
    args : string typed list;
    exp : comp typed;
  }

  and comp =
    | CErr
    | CVal of value
    | CLetDeTu of {
        tulhs : string typed list;
        turhs : value typed;
        letbody : comp typed;
      }
    | CIte of { cond : value typed; et : comp typed; ef : comp typed }
    | CMatch of { matched : value typed; match_cases : match_case list }
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    | CApp of { appf : value typed; apparg : value typed }
    | CWithH of { handler : handler typed; handled_prog : comp typed }
    | CAppOp of { op : Pmop.t typed; appopargs : value typed list }
    | CAppPerform of { effop : string typed; appopargs : value typed list }
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
  val mk_lam : string typed -> comp typed -> value typed
  val mk_id_function : t -> value typed
  val mk_fix : string typed -> string typed -> comp typed -> value typed
  val mk_lete : string typed -> comp typed -> comp typed -> comp typed
  val mk_app : value typed -> value typed -> comp typed
  val mk_withh : handler typed -> comp typed -> comp typed
  val mk_appop : Pmop.t typed -> value typed list -> comp typed
  val mk_perform : string typed -> value typed list -> comp typed
  val var_to_str : comp typed -> string typed
  val layout_value : value typed -> string
  val layout_id : string typed -> string
  val layout_op : Pmop.t typed -> string
  val layout_handler : handler typed -> string
  val layout_match_case : match_case -> string
  val layout_comp : comp typed -> string
  val do_subst_value : string * value typed -> value typed -> value typed
  val do_subst_comp : string * value typed -> comp typed -> comp typed

  val do_multisubst_value :
    (string * value typed) list -> value typed -> value typed

  val do_multisubst_comp :
    (string * value typed) list -> comp typed -> comp typed
end

module F (Ty : Typed.T) : T with type t = Ty.t and type 'a typed = 'a Ty.typed =
struct
  open Sexplib.Std

  type constant = Constant.t [@@deriving sexp]

  include Ty

  type value =
    | VVar of string
    | VConst of constant
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VFix of {
        fixname : string typed;
        fixarg : string typed;
        fixbody : comp typed;
      }
    | VTu of value typed list
    | VHd of handler typed

  and handler_case = {
    effop : string typed;
    effargs : string typed list;
    effk : string typed;
    hbody : comp typed;
  }

  and ret_case = { retarg : string typed; retbody : comp typed }
  and handler = { ret_case : ret_case; handler_cases : handler_case list }

  and match_case = {
    constructor : Pmop.t typed;
    args : string typed list;
    exp : comp typed;
  }

  and comp =
    | CErr
    | CVal of value
    | CLetDeTu of {
        tulhs : string typed list;
        turhs : value typed;
        letbody : comp typed;
      }
    | CIte of { cond : value typed; et : comp typed; ef : comp typed }
    | CMatch of { matched : value typed; match_cases : match_case list }
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    | CApp of { appf : value typed; apparg : value typed }
    | CWithH of { handler : handler typed; handled_prog : comp typed }
    | CAppOp of { op : Pmop.t typed; appopargs : value typed list }
    | CAppPerform of { effop : string typed; appopargs : value typed list }
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

  let mk_lam lamarg lambody =
    (VLam { lamarg; lambody }) #: (mk_arr lamarg.ty lambody.ty)

  let mk_id_function ty =
    let lamarg = "x" #: ty in
    (VLam { lamarg; lambody = (CVal (VVar "x")) #: ty }) #: (mk_arr ty ty)

  let mk_fix fixname fixarg fixbody =
    (VFix { fixname; fixarg; fixbody }) #: fixname.ty

  let mk_lete lhs rhs letbody = (CLetE { lhs; rhs; letbody }) #: letbody.ty
  let mk_app appf apparg = (CApp { appf; apparg }) #: (get_retty appf.ty)

  let mk_withh handler handled_prog =
    (CWithH { handler; handled_prog }) #: (get_retty handler.ty)

  let mk_appop op appopargs =
    (CAppOp { op; appopargs }) #: (snd @@ destruct_arr_tp op.ty)

  let mk_perform effop appopargs =
    (CAppPerform { effop; appopargs }) #: (snd @@ destruct_arr_tp effop.ty)

  open Zzdatatype.Datatype

  let rec layout_value (v : value typed) : string =
    layout_typed
      (function
        | VVar name -> name
        | VConst const -> Constant.layout const
        | VLam { lamarg; lambody } ->
            spf "(fun %s -> %s)" (layout_id lamarg) (layout_comp lambody)
        | VFix { fixname; fixarg; fixbody } ->
            spf "(fun fix_%s %s -> %s)" (layout_id fixname) (layout_id fixarg)
              (layout_comp fixbody)
        | VTu vs -> spf "(%s)" @@ List.split_by_comma layout_value vs
        | VHd hd -> layout_handler hd)
      v

  and layout_id = layout_typed (fun x -> x)
  and layout_op op = Pmop.t_to_string op.x

  and layout_handler hd =
    layout_typed
      (fun { ret_case; handler_cases } ->
        let ret_case_str =
          spf "retc: fun %s -> %s"
            (layout_id ret_case.retarg)
            (layout_comp ret_case.retbody)
        in
        let handler_case_strs =
          List.map
            (fun case ->
              spf "%s: fun %s %s -> %s" (layout_id case.effop)
                (layout_id case.effk)
                (List.split_by " " layout_id case.effargs)
                (layout_comp case.hbody))
            handler_cases
        in
        spf "{%s}"
          (List.split_by "; " (fun x -> x) (ret_case_str :: handler_case_strs)))
      hd

  and layout_match_case { constructor; args; exp } =
    spf "%s (%s) -> %s" (layout_op constructor)
      (List.split_by_comma (fun x -> x.x) args)
      (layout_comp exp)

  and layout_comp (comp : comp typed) : string =
    layout_typed
      (fun (compx : comp) ->
        match compx with
        | CErr -> "Err"
        | CVal v -> layout_value { x = v; ty = comp.ty }
        | CLetDeTu { tulhs; turhs; letbody } ->
            spf "let (%s) = %s in %s"
              (List.split_by_comma layout_id tulhs)
              (layout_value turhs) (layout_comp letbody)
        | CIte { cond; et; ef } ->
            spf "if %s then %s else %s" (layout_value cond) (layout_comp et)
              (layout_comp ef)
        | CMatch { matched; match_cases } ->
            spf "match %s with %s" (layout_value matched)
              (List.split_by " | " layout_match_case match_cases)
        | CLetE { lhs; rhs; letbody } ->
            spf "let %s = %s in %s" (layout_id lhs) (layout_comp rhs)
              (layout_comp letbody)
        | CApp { appf; apparg } ->
            spf "%s %s" (layout_value appf) (layout_value apparg)
        | CWithH { handler; handled_prog } ->
            spf "(match_with %s %s)" (layout_comp handled_prog)
              (layout_handler handler)
        | CAppOp { op; appopargs } ->
            spf "%s (%s)" (layout_op op)
              (List.split_by_comma layout_value appopargs)
        | CAppPerform { effop; appopargs } ->
            spf "peform %s (%s)" (layout_id effop)
              (List.split_by_comma layout_value appopargs))
      comp

  let rec do_subst_value (x, v) e : value typed =
    match e.x with
    | VVar y -> if String.equal x y then v else e
    | VConst _ -> e
    | VLam { lamarg; lambody } ->
        if String.equal lamarg.x x then e
        else (VLam { lamarg; lambody = do_subst_comp (x, v) lambody }) #: e.ty
    | VFix { fixname; fixarg; fixbody } ->
        if String.equal fixname.x x || String.equal fixarg.x x then e
        else
          (VFix { fixname; fixarg; fixbody = do_subst_comp (x, v) fixbody })
          #: e.ty
    | VTu vs -> (VTu (List.map (do_subst_value (x, v)) vs)) #: e.ty
    | VHd hd -> (VHd (do_subst_handler (x, v) hd)) #: e.ty

  and do_subst_handler (x, v) hd =
    let { ret_case; handler_cases } = hd.x in
    let ret_case =
      if String.equal ret_case.retarg.x x then ret_case
      else { ret_case with retbody = do_subst_comp (x, v) ret_case.retbody }
    in
    let handler_cases =
      List.map
        (fun case ->
          if
            String.equal case.effk.x x
            || List.exists (fun y -> String.equal x y.x) case.effargs
          then case
          else { case with hbody = do_subst_comp (x, v) case.hbody })
        handler_cases
    in
    { ret_case; handler_cases } #: hd.ty

  and do_subst_match_case (x, v) { constructor; args; exp } =
    let exp =
      if List.exists (fun y -> String.equal x y.x) args then exp
      else do_subst_comp (x, v) exp
    in
    { constructor; args; exp }

  and do_subst_comp (x, v) e : comp typed =
    let ex =
      match e.x with
      | CErr -> CErr
      | CVal value -> CVal (do_subst_value (x, v) value #: e.ty).x
      | CLetDeTu { tulhs; turhs; letbody } ->
          let letbody =
            if List.exists (fun y -> String.equal x y.x) tulhs then letbody
            else do_subst_comp (x, v) letbody
          in
          CLetDeTu { tulhs; turhs = do_subst_value (x, v) turhs; letbody }
      | CIte { cond; et; ef } ->
          CIte
            {
              cond = do_subst_value (x, v) cond;
              et = do_subst_comp (x, v) et;
              ef = do_subst_comp (x, v) ef;
            }
      | CMatch { matched; match_cases } ->
          CMatch
            {
              matched = do_subst_value (x, v) matched;
              match_cases = List.map (do_subst_match_case (x, v)) match_cases;
            }
      | CLetE { lhs; rhs; letbody } ->
          let letbody =
            if String.equal lhs.x x then letbody
            else do_subst_comp (x, v) letbody
          in
          CLetE { lhs; rhs = do_subst_comp (x, v) rhs; letbody }
      | CApp { appf; apparg } ->
          CApp
            {
              appf = do_subst_value (x, v) appf;
              apparg = do_subst_value (x, v) apparg;
            }
      | CWithH { handler; handled_prog } ->
          CWithH
            {
              handler = do_subst_handler (x, v) handler;
              handled_prog = do_subst_comp (x, v) handled_prog;
            }
      | CAppOp { op; appopargs } ->
          CAppOp { op; appopargs = List.map (do_subst_value (x, v)) appopargs }
      | CAppPerform { effop; appopargs } ->
          CAppPerform
            { effop; appopargs = List.map (do_subst_value (x, v)) appopargs }
    in
    ex #: e.ty

  let do_multisubst_value (l : (string * value typed) list) (comp : value typed)
      : value typed =
    List.fold_right do_subst_value l comp

  let do_multisubst_comp (l : (string * value typed) list) (comp : comp typed) :
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
