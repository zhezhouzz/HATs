module type T = sig
  include Typed.T

  type value =
    | VVar of string
    | VConst of Constant.t
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VFix of {
        fixname : string typed;
        fixarg : string typed;
        fixbody : comp typed;
      }
    | VTu of value typed list

  and match_case = {
    constructor : string typed;
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
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    (* | CIte of { cond : value typed; et : comp typed; ef : comp typed } *)
    | CMatch of { matched : value typed; match_cases : match_case list }
    | CApp of { appf : value typed; apparg : value typed }
    | CAppOp of { op : Op.t typed; appopargs : value typed list }
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
  val lam_to_fix : string typed -> value typed -> value typed
  val lam_to_fix_comp : string typed -> comp typed -> comp typed
  val mk_lete : string typed -> comp typed -> comp typed -> comp typed
  val mk_app : value typed -> value typed -> comp typed
  val mk_appop : Op.t typed -> value typed list -> comp typed
  val var_to_str : comp typed -> string typed
  val do_subst_value : string * value typed -> value typed -> value typed
  val do_subst_comp : string * value typed -> comp typed -> comp typed

  val do_multisubst_value :
    (string * value typed) list -> value typed -> value typed

  val do_multisubst_comp :
    (string * value typed) list -> comp typed -> comp typed

  val stat_count_comp_branchs : comp typed -> int
  val stat_count_value_branchs : value typed -> int
  val stat_count_comp_vars : comp typed -> int
  val stat_count_value_vars : value typed -> int
  val stat_is_rec : comp typed -> bool
end

module F (Ty : Typed.T) : T with type t = Ty.t and type 'a typed = 'a Ty.typed =
struct
  open Sexplib.Std
  include Ty

  type value =
    | VVar of string
    | VConst of Constant.t
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VFix of {
        fixname : string typed;
        fixarg : string typed;
        fixbody : comp typed;
      }
    | VTu of value typed list

  and match_case = {
    constructor : string typed;
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
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    (* | CIte of { cond : value typed; et : comp typed; ef : comp typed } *)
    | CMatch of { matched : value typed; match_cases : match_case list }
    | CApp of { appf : value typed; apparg : value typed }
    | CAppOp of { op : Op.t typed; appopargs : value typed list }
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

  let stat_is_rec comp =
    match comp.x with
    | CVal (VFix _) -> true
    | CVal (VLam _) -> false
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let rec stat_count_comp_branchs comp =
    let rec aux comp =
      match comp.x with
      | CErr | CApp _ | CAppOp _ -> 1
      | CVal v -> stat_count_value_branchs v #: comp.ty
      | CLetDeTu { letbody; _ } -> aux letbody
      | CMatch { match_cases; _ } ->
          let bs = List.map (fun { exp; _ } -> aux exp) match_cases in
          List.fold_left (fun sum n -> sum + n) 0 bs
      | CLetE { letbody; _ } -> aux letbody
    in
    aux comp

  and stat_count_value_branchs comp : int =
    let aux v =
      match v.x with
      | VVar _ | VConst _ | VTu _ -> 1
      | VLam { lambody; _ } -> stat_count_comp_branchs lambody
      | VFix { fixbody; _ } -> stat_count_comp_branchs fixbody
    in
    aux comp

  let rec stat_count_comp_vars comp =
    let rec aux comp =
      match comp.x with
      | CErr | CApp _ | CAppOp _ -> 0
      | CVal v -> stat_count_value_vars v #: comp.ty
      | CLetDeTu { letbody; _ } -> 1 + aux letbody
      | CMatch { match_cases; _ } ->
          let bs =
            List.map
              (fun { args; exp; _ } -> List.length args + aux exp)
              match_cases
          in
          List.fold_left (fun sum n -> sum + n) 0 bs
      | CLetE { letbody; _ } -> 1 + aux letbody
    in
    aux comp

  and stat_count_value_vars comp =
    let aux v =
      match v.x with
      | VVar _ | VConst _ | VTu _ -> 1
      | VLam { lambody; _ } -> stat_count_comp_vars lambody
      | VFix { fixbody; _ } -> stat_count_comp_vars fixbody
    in
    aux comp

  let to_v_ = function
    | CVal x -> x
    | _ -> _failatwith __FILE__ __LINE__ "not a value"

  let var_to_str_ = function
    | CVal (VVar x) -> x
    | _ -> _failatwith __FILE__ __LINE__ "not a var"

  let to_comp_ v = CVal v
  let to_v x = to_v_ #-> x
  let to_comp x = to_comp_ #-> x
  let var_to_str x = var_to_str_ #-> x

  let mk_lam lamarg lambody =
    (VLam { lamarg; lambody }) #: (mk_arr lamarg.ty lambody.ty)

  let mk_id_function ty =
    let lamarg = "x" #: ty in
    (VLam { lamarg; lambody = (CVal (VVar "x")) #: ty }) #: (mk_arr ty ty)

  let mk_fix fixname fixarg fixbody =
    (VFix { fixname; fixarg; fixbody }) #: fixname.ty

  let lam_to_fix fixname (body : value typed) : value typed =
    match body.x with
    | VLam { lamarg; lambody } -> mk_fix fixname lamarg lambody
    | _ -> _failatwith __FILE__ __LINE__ ""

  let lam_to_fix_comp fixname (body : comp typed) : comp typed =
    to_comp (lam_to_fix fixname (to_v body))

  let mk_lete lhs rhs letbody = (CLetE { lhs; rhs; letbody }) #: letbody.ty
  let mk_app appf apparg = (CApp { appf; apparg }) #: (get_retty appf.ty)

  let mk_appop op appopargs =
    (CAppOp { op; appopargs }) #: (snd @@ destruct_arr_tp op.ty)

  open Zzdatatype.Datatype

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
      (* | CIte { cond; et; ef } -> *)
      (*     CIte *)
      (*       { *)
      (*         cond = do_subst_value (x, v) cond; *)
      (*         et = do_subst_comp (x, v) et; *)
      (*         ef = do_subst_comp (x, v) ef; *)
      (*       } *)
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
      | CAppOp { op; appopargs } ->
          CAppOp { op; appopargs = List.map (do_subst_value (x, v)) appopargs }
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
