From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import BasicTyping.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

Definition substitution := amap constant.

Definition substution_eq_up_to_d (d: aset) (m m': substitution) :=
  forall (x: atom), x ∈ d -> m !! x = m' !! x.

Notation "m 'd≡{' d '}' m' " := (substution_eq_up_to_d d m m') (at level 20, d constr).

Lemma empty_map_dom_is_empty: dom aset (∅ : substitution) = ∅.
Proof. fast_set_solver. Qed.

#[global]
Instance substitution_stale : @Stale aset substitution := dom aset.
Arguments substitution_stale /.

(** subst *)
(** The bprop type only works for the value with the base type (constants), thus the subst over lambda terms doesn't (shouldn't) works; and we should never update a non-lc term (e.g., vbvar _). *)
(** The subst should guarantee: *)
(** 1. the variable x1 is not in in the current substitution. *)
(** 2. if the value v2 is a free variable x2, it should be in the current substitution, but not used in the further bprops. *)

Definition substitution_insert_value: atom -> value -> substitution -> substitution :=
  fun x1 v2 st => match v2 with
               | vfvar x2 =>
                   match st !! x2 with
                   | None => st (** this case should never happen *)
                   | Some c2 => <[x1 := c2]> st
                   end
               | vconst c2 => (<[x1 := c2]> st)
               | vbvar _ => st
               | vlam _ _ => st
               | vfix _ _ => st
               end.

Notation " '{' x '↦' v '}' " := (substitution_insert_value x v) (at level 20, format "{ x ↦ v }", x constr, v constr).

Definition substitution_subst_var (a b: atom) (st: substitution) :=
  match st !! b with
  | None => delete a st
  | Some c => <[a := c]> st
  end.

Definition substitution_subst: aset -> atom -> value -> substitution -> substitution :=
  fun d x1 v2 st =>
    if decide (x1 ∈ d) then
      match v2 with
      | vfvar x2 =>
          if decide (x2 ∈ d) then
            substitution_subst_var x1 x2 st
          else st
      | vconst c2 => <[x1 := c2]> st
      | vbvar _ => st
      | vlam _ _ => st
      | vfix _ _ => st
      end
    else st.

Notation " '{' x ':={' d '}' v '}' " := (substitution_subst d x v) (at level 20, format "{ x :={ d } v }", x constr, v constr).

(** bound substitution works like vfbar, which is a finite map with a bound. *)
Definition bsubstitution := nat -> constant.
(* Inductive bsubstitution : Type := *)
(* | bsubstitution_ (n: nat) (bst: nat -> constant). *)

Definition bsubstution_eq_up_to_n (n: nat) (bst1 bst2: bsubstitution) :=
  forall i, i < n -> bst1 i = bst2 i.

Notation "m 'n≡{' n '}' m' " := (bsubstution_eq_up_to_n n m m') (at level 20, n constr).

Definition bsubstitution_insert (k: nat) (c: constant) (bst: bsubstitution) := fun i => if decide (i = k) then c else bst i.

Definition bsubstitution_push (c: constant) (bst: bsubstitution) : bsubstitution := fun i => match i with 0 => c | S i => bst i end.

Definition bsubstitution_emp: bsubstitution := fun _ => 0.

Notation "b∅" := bsubstitution_emp (format "b∅").
Notation " '<b[' k ':=' c ']>' " := (bsubstitution_insert k c) (at level 5, right associativity, format "<b[ k := c ]>", c constr).
Notation " '<b[↦' c ']>' " := (bsubstitution_push c) (at level 5, right associativity, format "<b[↦ c ]>", c constr).

Definition ty_of_substitution (st: substitution) : amap base_ty := ty_of_const <$> st.
