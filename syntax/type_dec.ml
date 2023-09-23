module NT = Normalty.Ntyped

type constructor_declaration = { constr_name : string; argsty : NT.t list }

type t = {
  type_name : string;
  type_params : NT.t list;
  type_decls : constructor_declaration list;
}

type user_defined_types = t list

open NT

let name_to_ctype name type_params = Ty_constructor (name, type_params)

let mk_constr_types { constr_name; argsty } retty =
  (Op.DtOp constr_name) #: (construct_arr_tp (argsty, retty))

open Zzdatatype.Datatype

let mk_ctx_ { type_name; type_params; type_decls } =
  let open Sugar in
  match type_name with
  | "effect" ->
      List.map
        (fun x ->
          match x.argsty with
          | [ ty ] -> (Op.EffOp x.constr_name) #: ty
          | _ -> _failatwith __FILE__ __LINE__ "?")
        type_decls
  | _ ->
      let retty = name_to_ctype type_name type_params in
      List.map (fun x -> mk_constr_types x retty) type_decls

let mk_ctx es = List.concat @@ List.map mk_ctx_ es
