From stdpp Require Import mapset.
From CT Require Import CoreLangProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

Definition ty_of_const (c: constant): base_ty :=
  match c with
  | cnat _ => TNat
  | cbool _ => TBool
  end.

Definition ret_ty_of_op (op: effop): base_ty :=
  match op with
  | op_plus_one => TNat
  | op_minus_one => TNat
  | op_eq_zero => TBool
  | op_rannat => TNat
  | op_ranbool => TBool
  | op_read => TNat
  | op_write => TBool
  end.

Definition ty_of_op (op: effop): ty := TNat ⤍ (ret_ty_of_op op).

Definition context := amap ty.
#[global]
Instance context_stale : Stale context := dom.
Arguments context_stale /.

Reserved Notation "Γ '⊢t' t '⋮t' T" (at level 40).
Reserved Notation "Γ '⊢t' t '⋮v' T" (at level 40).

(** Basic typing rules  *)
Inductive tm_has_type : context -> tm -> ty -> Prop :=
| BtValue : forall Γ v T, Γ ⊢t v ⋮v T -> Γ ⊢t v ⋮t T
| BtLetE : forall Γ e1 e2 T1 T2 (L: aset),
    Γ ⊢t e1 ⋮t T1 ->
    (forall (x: atom), x ∉ L -> (<[ x := T1]> Γ) ⊢t e2 ^t^ x ⋮t T2) ->
    Γ ⊢t (tlete e1 e2) ⋮t T2
| BtEffOp : forall Γ (op: effop) v1 e (T1 Tx: base_ty) T (L: aset),
    Γ ⊢t v1 ⋮v T1 ->
    (ty_of_op op) = T1 ⤍ Tx ->
    (forall (x: atom), x ∉ L -> (<[x := TBase Tx]> Γ) ⊢t e ^t^ x ⋮t T) ->
    Γ ⊢t tleteffop op v1 e ⋮t T
| BtApp : forall Γ v1 v2 e T1 Tx T (L: aset),
    Γ ⊢t v1 ⋮v T1 ⤍ Tx ->
    Γ ⊢t v2 ⋮v T1 ->
    (forall (x: atom), x ∉ L -> (<[x := Tx]> Γ) ⊢t e ^t^ x ⋮t T) ->
    Γ ⊢t tletapp v1 v2 e ⋮t T
| BtMatchb: forall Γ v e1 e2 T,
    Γ ⊢t v ⋮v TBool ->
    Γ ⊢t e1 ⋮t T ->
    Γ ⊢t e2 ⋮t T ->
    Γ ⊢t (tmatchb v e1 e2) ⋮t T
with value_has_type : context -> value -> ty -> Prop :=
| BtConst : forall Γ (c: constant), Γ ⊢t c ⋮v (ty_of_const c)
| BtVar : forall Γ (x: atom) T,
    Γ !! x = Some T -> Γ ⊢t x ⋮v T
| BtFun : forall Γ Tx T e (L: aset),
    (forall (x: atom), x ∉ L -> (<[x := Tx]> Γ) ⊢t e ^t^ x ⋮t T) ->
    Γ ⊢t vlam Tx e ⋮v Tx ⤍ T
| BtFix : forall Γ (Tx: base_ty) T e (L: aset),
    (forall (x: atom), x ∉ L -> (<[x := TBase Tx]>Γ) ⊢t (vlam (Tx ⤍ T) e) ^v^ x ⋮v ((Tx ⤍ T) ⤍ T)) ->
    Γ ⊢t vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e) ⋮v Tx ⤍ T
where "Γ '⊢t' t '⋮t' T" := (tm_has_type Γ t T) and "Γ '⊢t' t '⋮v' T" := (value_has_type Γ t T).

Scheme value_has_type_mutual_rec := Induction for value_has_type Sort Prop
    with tm_has_type_mutual_rec := Induction for tm_has_type Sort Prop.

Global Hint Constructors tm_has_type: core.
Global Hint Constructors value_has_type: core.

Lemma basic_typing_contains_fv_tm: forall Γ e T, Γ ⊢t e ⋮t T -> fv_tm e ⊆ dom Γ
with basic_typing_contains_fv_value: forall Γ e T, Γ ⊢t e ⋮v T -> fv_value e ⊆ dom Γ.
Proof.
  all:
  destruct 1; simpl; eauto;
  try select (forall x, _ ∉ _ -> _) (fun H => auto_pose_fv x; repeat specialize_with x);
  repeat select (_ ⊢t _ ⋮v _) (fun H => apply basic_typing_contains_fv_value in H);
  repeat select (_ ⊢t _ ⋮t _) (fun H => apply basic_typing_contains_fv_tm in H);
  simpl in *;
  repeat
    match goal with
    | H : fv_tm ({_ ~t> _} _) ⊆ _ |- _ =>
        setoid_rewrite <- open_fv_tm' in H
    | H : _ ⊆ dom (<[_:=_]>_) |- _ =>
        setoid_rewrite dom_insert in H
    | H : _ !! _ = _ |- _ =>
        apply elem_of_dom_2 in H
    end;
  my_set_solver.
Qed.

Ltac instantiate_atom_listctx :=
  let acc := collect_stales tt in
  instantiate (1 := acc); intros;
  repeat (match goal with
          | [H: forall (x: atom), x ∉ ?L -> _, H': ?a ∉ _ ∪ (stale _) |- _ ] =>
              assert (a ∉ L) as Htmp by fast_set_solver;
              specialize (H a Htmp); clear Htmp; repeat destruct_hyp_conj; auto
          end; simpl).

Lemma basic_typing_regular_value: forall Γ v t, Γ ⊢t v ⋮v t -> lc v
with basic_typing_regular_tm: forall Γ e t, Γ ⊢t e ⋮t t -> lc e.
Proof.
  all: destruct 1; simpl;
    try econstructor; try instantiate_atom_listctx; eauto.
Qed.

Ltac basic_typing_regular_simp :=
  repeat match goal with
    | [H: _ ⊢t _ ⋮v _ |- lc _] => apply basic_typing_regular_value in H; destruct H; auto
    | [H: _ ⊢t _ ⋮t _ |- lc _] => apply basic_typing_regular_tm in H; destruct H; auto
    | [H: _ ⊢t _ ⋮v _ |- body _] => apply basic_typing_regular_value in H; destruct H; auto
    | [H: _ ⊢t _ ⋮t _ |- body _] => apply basic_typing_regular_tm in H; destruct H; auto
    end.

Lemma empty_basic_typing_bool_value_exists: forall (v: value), ∅ ⊢t v ⋮v TBool -> v = true \/ v = false.
Proof.
  inversion 1; subst; simpl in *.
  destruct c; simplify_eq. destruct b; eauto.
  simplify_map_eq.
Qed.

Lemma empty_basic_typing_nat_value_exists: forall (v: value), ∅ ⊢t v ⋮v TNat -> (exists (i: nat), v = i).
Proof.
  inversion 1; subst; simpl in *.
  destruct c; simplify_eq. eauto.
  simplify_map_eq.
Qed.

Lemma empty_basic_typing_base_const_exists: forall (v: value) (B: base_ty), ∅ ⊢t v ⋮v B -> (exists (c: constant), v = c).
Proof.
  inversion 1; subst. eauto. simplify_map_eq.
Qed.

Lemma empty_basic_typing_arrow_value_lam_exists:
  forall (v: value) T1 T2, ∅ ⊢t v ⋮v T1 ⤍ T2 ->
                      (exists e, v = vlam T1 e) \/ (exists e, v = vfix (T1 ⤍ T2) (vlam (T1 ⤍ T2) e)).
Proof.
  inversion 1; subst. simplify_map_eq.
  - left. eauto.
  - right. eexists. f_equal.
Qed.
