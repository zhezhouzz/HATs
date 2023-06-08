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
Import Equation.

Definition env := amap value.

Fixpoint value_msubst (env: env) (v : value): value :=
  match v with
  | vconst _ => v
  | vfvar y => match env !! y with
              | None => v
              | Some s => s
              end
  | vbvar _ => v
  | vlam T e => vlam T (tm_msubst env e)
  | vfix Tf e => vfix Tf (tm_msubst env e)
  end
with tm_msubst (env: env) (e : tm): tm :=
       match e with
       | treturn v => treturn (value_msubst env v)
       | tlete e1 e2 => tlete (tm_msubst env e1) (tm_msubst env e2)
       | tletapp v1 v2 e => tletapp (value_msubst env v1) (value_msubst env v2) (tm_msubst env e)
       | tleteffop op v1 e => tleteffop op (value_msubst env v1) (tm_msubst env e)
       | tmatchb v e1 e2 => tmatchb (value_msubst env v) (tm_msubst env e1) (tm_msubst env e2)
       end.

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

Definition termRraw (α: trace) Γ e e' :=
  forall Γv β (v: value), instantiation Γ Γv ->
                   α ⊧ tm_msubst Γv e ↪*{ β } v ->
                   α ⊧ tm_msubst Γv e' ↪*{ β } v.

Inductive termR: trace -> amap ty -> ty -> tm -> tm -> Prop :=
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

