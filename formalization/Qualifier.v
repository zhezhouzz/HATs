From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Substitution.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Substitution.

(** * We define the bound proposition in locally nameless style. *)

(** In order to defined the type denotation (logical relation) which is a recursive function, we should make sure the bprop type is structurally decreasing, which means we cannot do substution (or open, close) over the bprop types. Thus we lift all substition (open, close) into substitutions: bsubstitution is for bound variables, substitution is for free variables. *)
Definition bprop : Type := bsubstitution -> substitution -> Prop.

Inductive qualifier : Type :=
| qual (n: nat) (d: aset) (p: bprop).

Notation "'bp[' n '|' d '|' p ']'" := (qual n d p) (at level 5, format "bp[ n | d | p ]", p constr).

(** free variables *)
Definition qualifier_fv ϕ : aset :=
  match ϕ with
  | qual _ d _ => d
  end.

#[global]
Instance qualifier_stale : @Stale aset qualifier := qualifier_fv.
Arguments qualifier_stale /.

(** open; here we still open to a value *)
Definition bprop_open (k: nat) (s: value) (ϕ: bprop) : bprop :=
  fun bst (st: substitution) => ϕ (match s with
                | vfvar x =>
                    match st !! x with
                    | None => <b[ k := false ]> bst (* this case should never happen *)
                    | Some c => <b[ k := c ]> bst
                    end
                | vconst c => <b[ k := c ]> bst
                | vbvar _ => bst
                | vlam _ _ => bst
                | vfix _ _ => bst
                end) st.

Notation "'{' k '~bp>' s '}' e" := (bprop_open k s e) (at level 20, k constr).
Notation "e '^bp^' s" := (bprop_open 0 s e) (at level 20).

Definition dset_open (k: nat) (s: value) (d: aset) : aset :=
  match s with
  | vfvar x => {[x]} ∪ d
  | vconst c => d
  | vbvar _ => d
  | vlam _ _ => d
  | vfix _ _ => d
  end.

Definition qualifier_open (k: nat) (s: value) (ϕ: qualifier) : qualifier :=
  match ϕ with
  | qual n d p => qual (n `min` k) (dset_open k s d) (bprop_open k s p)
  end.

Notation "'{' k '~q>' s '}' e" := (qualifier_open k s e) (at level 20, k constr).
Notation "e '^q^' s" := (qualifier_open 0 s e) (at level 20).

Definition bprop_subst (x1: atom) (v2: value) (d: aset) (ϕ: bprop) : bprop :=
  (fun bst st => ϕ bst (substitution_subst d x1 v2 st)).

Definition dset_subst (x1: atom) (s: value) (d: aset) : aset :=
  if decide (x1 ∈ d) then
    match s with
    | vfvar x =>
        if decide (x ∈ d) then
          if decide (x1 = x) then d else (d ∖ {[x1]})
        else d
    | vconst c => d ∖ {[x1]}
    | vbvar _ => d
    | vlam _ _ => d
    | vfix _ _ => d
    end
  else
    d.

Definition qualifier_subst (x1: atom) (v2: value) (ϕ: qualifier) : qualifier :=
  match ϕ with
  | bp[ n | d | p ] => bp[ n | dset_subst x1 v2 d | bprop_subst x1 v2 d p ]
  end.

Notation "'{' x ':=' s '}q'" := (qualifier_subst x s) (at level 20, format "{ x := s }q", x constr).

(** well formed, locally closed, closed with substitution *)

Definition not_fv_in_bprop (d: aset) (ϕ: bprop) :=
  forall (m m': substitution), m d≡{d} m' -> forall bst, ϕ bst m <-> ϕ bst m'.

Definition bound_in_bprop (bound: nat) (ϕ: bprop) :=
  forall (bst bst': bsubstitution) (st: substitution), bst n≡{ bound } bst' -> ϕ bst st <-> ϕ bst' st.

Lemma bound_in_bprop_0: forall ϕ,
    bound_in_bprop 0 ϕ -> (forall bst bst' st, ϕ bst st <-> ϕ bst' st).
Proof.
  intros. apply H. intros. intro n. intros. exfalso. lia.
Qed.

Lemma not_in_aset_implies_same_in_bprop: forall (d: aset) (ϕ: bprop),
    not_fv_in_bprop d ϕ ->
    forall (x: atom), x ∉ d -> forall (m: substitution), forall bst v_x, ϕ bst ({x :={d} v_x} m) <-> ϕ bst m.
Admitted.

Inductive valid_qualifier: qualifier -> Prop :=
| valid_qualifier_ : forall (n: nat) (d: aset) (p: bprop),
    not_fv_in_bprop d p -> bound_in_bprop n p -> valid_qualifier bp[ n | d | p ].

Inductive lc_qualifier_idx: nat -> qualifier -> Prop :=
| lc_qualifier_idx_ : forall (m: nat) (n: nat) (d: aset) (p: bprop),
    n <= m -> lc_qualifier_idx m bp[ n | d | p ].

Definition mk_q_eq_constant c := bp[ 1 | ∅ | fun bst _ => (bst 0) = c ].
Definition mk_q_under_bot := bp[ 0 | ∅ | fun _ _ => False ].
Definition mk_q_under_top := bp[ 0 | ∅ | fun _ _ => True ].
Definition mk_q_eq_var (x: atom) := bp[ 1 | {[x]} | fun bst st => Some (bst 0) = st !! x ].
