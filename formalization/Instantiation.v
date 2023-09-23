From stdpp Require Import mapset.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Trace.

Notation env := (amap value).

Definition closed_env (env : env) := map_Forall (fun _ => closed_value) env.

Definition msubst {A} (subst : atom -> value -> A -> A)
                  (env : env) (a : A) : A :=
  map_fold subst a env.

Definition instantiation (Γ: amap ty) (Γv: env) :=
  forall (x: atom),
    match Γ !! x with
    | None => Γv !! x = None
    | Some T =>
      match Γv !! x with
      | None => False
      | Some v => ∅ ⊢t v ⋮v T
      end
    end.

Definition termRraw (α: list evop) Γ e e' :=
  forall Γv β (v: value), instantiation Γ Γv ->
                   α ⊧ msubst tm_subst Γv e ↪*{ β } v ->
                   α ⊧ msubst tm_subst Γv e' ↪*{ β } v.

Inductive termR: list evop -> amap ty -> ty -> tm -> tm -> Prop :=
| termR_c: forall α Γ T (e e': tm),
    Γ ⊢t e ⋮t T -> Γ ⊢t e' ⋮t T ->
    termRraw α Γ e e' ->
    termR α Γ T e e'.

Notation " e1 '<-<{' α ';' Γ ';' T '}' e2 " := (termR α Γ T e1 e2)
                                                 (at level 10, format "e1 <-<{ α ; Γ ; T } e2", Γ constr, α constr, T constr).

Notation " e1 '<-<{' α ';' Γ '}' e2 " := (termRraw α Γ e1 e2)
                                                 (at level 10, format "e1 <-<{ α ; Γ } e2", Γ constr, α constr).

Lemma termRraw_refl: forall α Γ e, e <-<{ α ; Γ } e.
Proof.
  intros. intro; auto.
Qed.

Lemma termR_refl: forall α Γ e T, Γ ⊢t e ⋮t T -> e <-<{ α ; Γ ; T } e.
Proof.
  intros. constructor; auto. intro; auto.
Qed.

Lemma closed_env_insert env x v :
  env !! x = None ->
  closed_env (<[x:=v]>env) ->
  closed_value v /\ closed_env env.
Proof.
  intro.
  unfold closed_env.
  rewrite map_Forall_insert; eauto.
Qed.
