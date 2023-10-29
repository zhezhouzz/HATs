module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Sugar
open Zzdatatype.Datatype
open Syntax.RtyRaw

let get_denoteopt_from_attr a =
  match a with [ x ] -> Some x.attr_name.txt | _ -> None

let get_denoteopt expr = get_denoteopt_from_attr expr.pexp_attributes

let get_denote expr =
  match get_denoteopt expr with
  | Some x -> x
  | None -> _failatwith __FILE__ __LINE__ ""

let get_pat_denoteopt pat = get_denoteopt_from_attr pat.ppat_attributes

let get_pat_denote expr =
  match get_pat_denoteopt expr with
  | Some x -> x
  | None -> _failatwith __FILE__ __LINE__ ""

let force_last (vs : 'a list) =
  match List.last_destruct_opt vs with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some (vs, v) -> (vs, v)

let paren_stack_parsing lr str =
  let cL = String.get lr 0 in
  let cR = String.get lr 1 in
  let rec aux str num =
    if num <= 0 then false
    else
      match str with
      | [] -> num == 1
      | c :: str ->
          if Char.equal c cL then aux str (num + 1)
          else if Char.equal c cR then aux str (num - 1)
          else aux str num
  in
  let res = aux (List.of_seq @@ String.to_seq str) 1 in
  let () = Printf.printf "%s~[%s]: %b\n" lr str res in
  res

(* TODO: better has_paren *)
let has_paren str =
  if String.length str <= 2 then true
  else
    (* let c1 = String.get str 0 in *)
    (* let c2 = String.get str (String.length str - 1) in *)
    let c1c2 = String.sub str 0 1 ^ String.sub str (String.length str - 1) 1 in
    (* let rest = String.sub str 1 (String.length str - 2) in *)
    (* let () = Printf.printf "[has_paren]    %s %s\n" c1c2 rest in *)
    (* match spf "%c%c" c1 c2 with *)
    match c1c2 with
    | "()" | "{}" | "[]" | "⟨⟩" -> true
    (* | "()" -> paren_stack_parsing "()" rest *)
    (* | "{}" -> paren_stack_parsing "{}" rest *)
    (* | "[]" -> paren_stack_parsing "[]" rest *)
    (* | "⟨⟩" -> true (\* paren_stack_parsing "⟨⟩" rest *\) *)
    | _ -> false

let pprint_parn body = spf "{%s}" body
let layout_stropt = function None -> "" | Some x -> spf "%s:" x

(* let layout_arr = function PiArr -> "→" | SigamArr -> "⇢" *)
(* let force_paren str = if has_paren str then str else spf "(%s)" str *)

type layout_setting = {
  sym_true : string;
  sym_false : string;
  sym_and : string;
  sym_or : string;
  sym_not : string;
  sym_implies : string;
  sym_iff : string;
  sym_forall : string;
  sym_exists : string;
  layout_typedid : string Nt.typed -> string;
  layout_mp : string -> string;
}

let detailssetting =
  {
    sym_true = "⊤";
    sym_false = "⊥";
    sym_and = " ∧ ";
    sym_or = " ∨ ";
    sym_not = "¬";
    sym_implies = "=>";
    sym_iff = "<=>";
    sym_forall = "∀";
    sym_exists = "∃";
    layout_typedid = Nt.(fun x -> spf "(%s:%s)" x.x (layout x.ty));
    layout_mp = (fun x -> x);
  }

let psetting =
  {
    sym_true = "⊤";
    sym_false = "⊥";
    sym_and = " ∧ ";
    sym_or = " ∨ ";
    sym_not = "¬";
    sym_implies = "=>";
    sym_iff = "<=>";
    sym_forall = "∀";
    sym_exists = "∃";
    layout_typedid = (fun x -> x.x);
    (* (fun x ->          Printf.spf "(%s:%s)" x.x (Ty.layout x.ty)); *)
    layout_mp = (fun x -> x);
  }

let coqsetting =
  {
    sym_true = "True";
    sym_false = "False";
    sym_and = "/\\ ";
    sym_or = " \\/ ";
    sym_not = "~";
    sym_implies = "->";
    sym_iff = "<->";
    sym_forall = "forall";
    sym_exists = "exists";
    layout_typedid = (fun x -> x.x);
    layout_mp = (function "==" -> "=" | x -> x);
  }
