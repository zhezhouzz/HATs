module T = Language.TypedTermlang
open Language.TypedCoreEff

(* open Sugar *)
open Zzdatatype.Datatype

let rec denormalize_comp (comp : comp typed) : T.term T.typed =
  let compty = comp.ty in
  let res =
    match comp.x with
    | CErr -> T.Err
    | CVal v -> T.((denormalize_value v #: compty).x)
    | CLetDeTu { tulhs; turhs; letbody } ->
        T.(
          Let
            {
              if_rec = false;
              lhs = tulhs;
              rhs = denormalize_value turhs;
              letbody = denormalize_comp letbody;
            })
    | CIte { cond; et; ef } ->
        T.(
          Ite (denormalize_value cond, denormalize_comp et, denormalize_comp ef))
    | CMatch { matched; match_cases } ->
        T.(
          Match
            ( denormalize_value matched,
              List.map denormalize_match_case match_cases ))
    | CLetE { lhs; rhs; letbody } ->
        T.(
          Let
            {
              if_rec = false;
              lhs = [ lhs ];
              rhs = denormalize_comp rhs;
              letbody = denormalize_comp letbody;
            })
    | CApp { appf; apparg } ->
        T.(App (denormalize_value appf, [ denormalize_value apparg ]))
    | CWithH { handler = { x = handler; ty }; handled_prog } ->
        T.(
          CWithH
            {
              handler = (denormalize_handler handler) #: ty;
              handled_prog = denormalize_comp handled_prog;
            })
    | CAppOp { op; appopargs } ->
        T.(AppOp (op, List.map denormalize_value appopargs))
    | CAppPerform { effop; appopargs } ->
        T.(
          Perform
            { rhsop = effop; rhsargs = List.map denormalize_value appopargs })
  in
  T.(res #: compty)

and denormalize_value (value : value typed) : T.term T.typed =
  let valuety = value.ty in
  let res =
    match value.x with
    | VVar name -> T.Var name
    | VConst const -> T.Const const
    | VLam { lamarg; lambody } ->
        T.(Lam { lamarg; lambody = denormalize_comp lambody })
    | VFix { fixname; fixarg; fixbody } ->
        let open T in
        let lambody =
          (Lam { lamarg = fixarg; lambody = denormalize_comp fixbody })
          #: valuety
        in
        Lam { lamarg = fixname; lambody }
    | VTu vs -> T.(Tu (List.map denormalize_value vs))
    | VHd { x = hd; ty } -> T.(VHd (denormalize_handler hd) #: ty)
  in
  T.(res #: valuety)

and denormalize_match_case { constructor; args; exp } : T.match_case =
  T.{ constructor; args; exp = denormalize_comp exp }

and denormalize_handler_case { effop; effargs; effk; hbody } : T.handler_case =
  T.{ effop; effargs; effk; hbody = denormalize_comp hbody }

and denormalize_ret_case { retarg; retbody } : T.ret_case =
  T.{ retarg; retbody = denormalize_comp retbody }

and denormalize_handler { ret_case; handler_cases } : T.handler =
  T.
    {
      ret_case = denormalize_ret_case ret_case;
      handler_cases = List.map denormalize_handler_case handler_cases;
    }

let layout_comp comp = T.layout (denormalize_comp comp)
let layout_value comp = T.layout (denormalize_value comp)
