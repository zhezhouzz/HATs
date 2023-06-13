From stdpp Require Import mapset.
From stdpp Require Import natmap.
From stdpp Require Import fin vector.
From CT Require Import CoreLangProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

(** * We define the bound proposition in locally nameless style. *)

(** Qualifier is defined as a Coq proposition [prop], with closed arguments that
correspond to possibly open [vals]. We use [vec] to make sure [prop] arguments
and [vals] match exactly, but using [list] is probably fine too; in that case
[prop] is defined over possibly partial assignments. *)
Inductive qualifier : Type :=
| qual {n : nat} (vals : vec value n) (prop : vec constant n -> Prop).

(** For example, a qualifier may be: (with notation from stdpp)
<<
qual [# vbvar 0; vbvar 1; vfvar "x"]
   (fun v => v !!! 0 = v !!! 1 /\ v !!! 2 = cnat 1)%fin
>>
*)

Fixpoint denote_vals {n} (vals : vec value n) : option (vec constant n) :=
  match vals with
  | [#] => Some [#]
  | x ::: v =>
      match x with
      | vconst c =>
          match denote_vals v with
          | Some v' => Some (c ::: v')
          | None => None
          end
      | _ => None
      end
  end.

(** Denote a _closed_ qualifier to a Coq proposition. The result if [False] if the
qualifier mentions functions. *)
Definition denote_qualifier (ϕ : qualifier) : Prop :=
  match ϕ with
  | qual vals prop =>
      match denote_vals vals with
      | Some v => prop v
      | None => False
      end
  end.

(** free variables *)
Definition qualifier_fv ϕ : aset :=
  match ϕ with
  | qual vals _ => Vector.fold_right (fun v s => fv_value v ∪ s) vals ∅
  end.

#[global]
Instance qualifier_stale : @Stale aset qualifier := qualifier_fv.
Arguments qualifier_stale /.

Definition qualifier_open (k: nat) (s: value) (ϕ: qualifier) : qualifier :=
  match ϕ with
  | qual vals prop =>
      qual (vmap (open_value k s) vals) prop
  end.

Notation "'{' k '~q>' s '}' e" := (qualifier_open k s e) (at level 20, k constr).
Notation "e '^q^' s" := (qualifier_open 0 s e) (at level 20).

Definition qualifier_subst (x: atom) (v: value) (ϕ: qualifier) : qualifier :=
  match ϕ with
  | qual vals prop =>
      qual (vmap (value_subst x v) vals) prop
  end.

Notation "'{' x ':=' s '}q'" := (qualifier_subst x s) (at level 20, format "{ x := s }q", x constr).

Inductive lc_qualifier : qualifier -> Prop :=
| lc_qual n vals prop :
  Vector.Forall (fun v => lc (treturn v)) vals ->
  lc_qualifier (@qual n vals prop)
.

Definition qualifier_and (q1 q2 : qualifier) : qualifier :=
  match q1, q2 with
  | qual vals1 prop1, qual vals2 prop2 =>
      qual (vals1 +++ vals2)
        (fun v =>
           let (v1, v2) := Vector.splitat _ v
           in prop1 v1 /\ prop2 v2)
  end.

Definition mk_q_bvar_eq_val n v :=
  qual [# vbvar n; v] (fun v => v !!! 0 = v !!! 1)%fin.
Definition mk_q_under_bot := qual [#] (fun _ => False).
Definition mk_q_under_top := qual [#] (fun _ => True).

Notation " 'b0:v=' v " := (mk_q_bvar_eq_val 0 v)
                            (at level 5, format "b0:v= v", v constr).
Notation " 'b0:x=' y " := (mk_q_bvar_eq_val 0 (vfvar y))
                            (at level 5, format "b0:x= y", y constr).
Notation " 'b0:c=' c " := (mk_q_bvar_eq_val 0 (vconst c))
                            (at level 5, format "b0:c= c", c constr).
Notation " 'b1:v=' v " := (mk_q_bvar_eq_val 1 v)
                            (at level 5, format "b1:v= v", v constr).
Notation " 'b1:x=' y " := (mk_q_bvar_eq_val 1 (vfvar y))
                            (at level 5, format "b1:x= y", y constr).
Notation " 'b1:c=' c " := (mk_q_bvar_eq_val 1 (vconst c))
                            (at level 5, format "b1:c= c", c constr).
Notation " ϕ1 '&' ϕ2 " := (qualifier_and ϕ1 ϕ2)
                             (at level 5, format "ϕ1  &  ϕ2").

(* NOTE: the constant cases can be expressed directly without invoking
[mk_q_bvar_eq_val], e.g., [qual [# vbvar 0] (fun v => v !!! 0 = c)%fin]. But the
current encoding is more uniform. In addition, the following can be expressed
by combining [qualifier_and] and the existing notations. *)

(* Definition mk_q_1_eq_constant_0_eq_var c (x: atom) := *)
(*   qual [# vbvar 0; vbvar 1; vfvar x] (fun v => v !!! 1 = c /\ v !!! 0 = v !!! 2)%fin. *)
(* Definition mk_q_1_eq_var_0_eq_var (x: atom) (y: atom) := *)
(*   qual [# vbvar 0; vbvar 1; vfvar y; vfvar x] *)
(*     (fun v => v !!! 1 = v !!! 3 /\ v !!! 0 = v !!! 2 )%fin. *)
(* Notation " 'b1:x=' y '∧∧' 'b0:x=' x " := (mk_q_1_eq_var_0_eq_var y x) (at level 5, format "b1:x= y ∧∧ b0:x= x", y constr). *)
(* Notation " 'b1:c=' c '∧∧' 'b0:x=' x " := (mk_q_1_eq_constant_0_eq_var c x) (at level 5, format "b1:c= c ∧∧ b0:x= x", c constr). *)
