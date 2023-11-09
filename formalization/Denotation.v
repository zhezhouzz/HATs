From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Coq.Program Require Import Wf.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementType.
From CT Require Import Instantiation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import BasicTyping.
Import RefinementType.
Import Qualifier.
Import Trace.

(** Regular language *)

Definition valid_evop 'ev{op ~ argv := retv} :=
  ∅ ⊢t argv ⋮v TNat /\ ∅ ⊢t retv ⋮v ret_ty_of_op op.

Definition valid_trace := Forall valid_evop.

Fixpoint langA (a: am) (α: list evop) {struct a} : Prop :=
  closed_am ∅ a /\ valid_trace α /\
    match a with
    | aevent op ϕ =>
        exists (c1 c: constant) α',
          α = ev{op ~ c1 := c} :: α' /\
          denote_qualifier ({0 ~q> c} ({1 ~q> c1} ϕ))
    | aany => True
    | aconcat a1 a2 => exists α1 α2, α = α1 ++ α2 ∧ langA a1 α1 /\ langA a2 α2
    | aunion a1 a2 => langA a1 α ∨ langA a2 α
    end.

Notation "'a⟦' a '⟧' " := (langA a) (at level 20, format "a⟦ a ⟧", a constr).

(** Type Denotation: *)

(* Instead of addtion, we can also use [max] for the subterms. *)
Fixpoint pty_measure (ρ: pty) : nat :=
  match ρ with
  | {: _ | _} => 1
  | ρ ⇨ τ => 1 + pty_measure ρ + hty_measure τ
  | _ ⇢ ρ => 1 + pty_measure ρ
  end
with hty_measure (τ: hty) : nat :=
  match τ with
  | [: ρ | _ ▶ _ ] => 1 + pty_measure ρ
  | τ1 ⊓ τ2 => 1 + hty_measure τ1 + hty_measure τ2
  end .

(* The first argument is an overapproximation of the "size" of [ρ] or [τ]. In
other words, it is the "fuel" to get around Coq's termination checker. As long
as it is no less than [pty_measure] and [hty_measure], the denotation will not
hit bottom. Note that this is _different_ from the step used in step-indexed
logical relation. *)
Fixpoint ptyR (gas: nat) (ρ: pty) (e: tm) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
      ∅ ⊢t e ⋮t ⌊ ρ ⌋ /\ closed_pty ∅ ρ /\
        match ρ with
        | {: b | ϕ} =>
            forall (v: value) α β,
              α ⊧ e ↪*{β} v ->
              β = [] /\ denote_qualifier (ϕ ^q^ v)
        | B ⇢ ρ =>
            forall (v: value),
              ∅ ⊢t v ⋮v B ->
              ptyR gas' (ρ ^p^ v) e
        | ρx ⇨ τ =>
            forall (v_x: value),
              ptyR gas' ρx v_x ->
              htyR gas' (τ ^h^ v_x) (mk_app_e_v e v_x)
        end
  end

with htyR (gas: nat) (τ: hty) (e: tm) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
      ∅ ⊢t e ⋮t ⌊ τ ⌋ /\ closed_hty ∅ τ /\
        match τ with
        | [: ρ | A ▶ B ] =>
            forall (α β: list evop) (v: value),
              a⟦ A ⟧ α ->
              α ⊧ e ↪*{ β } v ->
              ptyR gas' ρ v /\ a⟦ B ⟧ (α ++ β)
        | τ1 ⊓ τ2 =>
            htyR gas' τ1 e /\ htyR gas' τ2 e
        end
  end.

Notation "'p⟦' ρ '⟧' " :=
  (ptyR (pty_measure ρ)  ρ) (at level 20, format "p⟦ ρ ⟧", ρ constr).

Notation "'⟦' τ '⟧' " := (htyR (hty_measure τ) τ) (at level 20, format "⟦ τ ⟧", τ constr).

Notation "'m{' x '}q'" := (msubst qualifier_subst x) (at level 20, format "m{ x }q", x constr).
Notation "'m{' x '}p'" := (msubst pty_subst x) (at level 20, format "m{ x }p", x constr).
Notation "'m{' x '}a'" := (msubst am_subst x) (at level 20, format "m{ x }a", x constr).
Notation "'m{' x '}h'" := (msubst hty_subst x) (at level 20, format "m{ x }h", x constr).
Notation "'m{' x '}v'" := (msubst value_subst x) (at level 20, format "m{ x }v", x constr).
Notation "'m{' x '}t'" := (msubst tm_subst x) (at level 20, format "m{ x }t", x constr).

Inductive ctxRst: listctx pty -> env -> Prop :=
| ctxRst0: ctxRst [] ∅
| ctxRst1: forall Γ env (x: atom) ρ (v: value),
    ctxRst Γ env ->
    (* [ok_ctx] implies [ρ] is closed and valid, meaning that it does not use
    any function variables. *)
    ok_ctx (Γ ++ [(x, ρ)]) ->
    p⟦ m{ env }p ρ ⟧ v ->
    ctxRst (Γ ++ [(x, ρ)]) (<[ x := v ]> env).

Lemma langA_closed a α :
  langA a α ->
  closed_am ∅ a.
Proof.
  destruct a; simpl; intuition.
Qed.

Lemma langA_valid_trace a α :
  langA a α ->
  valid_trace α.
Proof.
  destruct a; simpl; intuition.
Qed.

Lemma pty_measure_gt_0 ρ : pty_measure ρ > 0.
Proof.
  induction ρ; simpl; lia.
Qed.

Lemma hty_measure_gt_0 τ : hty_measure τ > 0.
Proof.
  induction τ; simpl; lia.
Qed.

Lemma pty_measure_S ρ : exists n, pty_measure ρ = S n.
Proof.
  destruct (Nat.lt_exists_pred 0 (pty_measure ρ)).
  pose proof (pty_measure_gt_0 ρ). lia.
  intuition eauto.
Qed.

Lemma hty_measure_S τ : exists n, hty_measure τ = S n.
  destruct (Nat.lt_exists_pred 0 (hty_measure τ)).
  pose proof (hty_measure_gt_0 τ). lia.
  intuition eauto.
Qed.

Lemma htyR_typed_closed gas τ e :
  htyR gas τ e ->
  ∅ ⊢t e ⋮t ⌊ τ ⌋ /\ closed_hty ∅ τ.
Proof.
  destruct gas; simpl; tauto.
Qed.

Lemma ptyR_typed_closed gas ρ e :
  ptyR gas ρ e ->
  ∅ ⊢t e ⋮t ⌊ ρ ⌋ /\ closed_pty ∅ ρ.
Proof.
  destruct gas; simpl; tauto.
Qed.

Lemma ptyR_closed_tm gas ρ e :
  ptyR gas ρ e ->
  closed_tm e.
Proof.
  intros H.
  apply ptyR_typed_closed in H.
  destruct H as (H&_).
  apply basic_typing_contains_fv_tm in H.
  my_set_solver.
Qed.

Lemma ptyR_closed_value gas ρ (v : value) :
  ptyR gas ρ v ->
  closed_value v.
Proof.
  intros H.
  apply ptyR_closed_tm in H.
  eauto.
Qed.

Lemma ptyR_lc gas ρ e :
  ptyR gas ρ e ->
  lc e.
Proof.
  intros H.
  apply ptyR_typed_closed in H.
  destruct H as (H&_).
  eauto using basic_typing_regular_tm.
Qed.

Lemma ctxRst_closed_env Γ Γv : ctxRst Γ Γv -> closed_env Γv.
Proof.
  unfold closed_env.
  induction 1.
  - apply map_Forall_empty.
  - apply map_Forall_insert_2; eauto.
    unfold closed_value.
    change (fv_value v) with (fv_tm v).
    apply equiv_empty.
    erewrite <- dom_empty.
    eapply basic_typing_contains_fv_tm.
    eapply ptyR_typed_closed.
    eauto.
Qed.

Lemma ctxRst_lc Γ Γv :
  ctxRst Γ Γv ->
  map_Forall (fun _ v => lc (treturn v)) Γv.
Proof.
  induction 1.
  apply map_Forall_empty.
  apply map_Forall_insert_2; eauto.
  apply ptyR_typed_closed in H1. simp_hyps.
  eauto using basic_typing_regular_tm.
Qed.

Lemma ctxRst_dom Γ Γv :
  ctxRst Γ Γv ->
  ctxdom Γ ≡ dom Γv.
Proof.
  induction 1; simpl; eauto.
  rewrite ctxdom_app_union.
  rewrite dom_insert.
  simpl. my_set_solver.
Qed.

Lemma ctxRst_ok_ctx Γ Γv :
  ctxRst Γ Γv ->
  ok_ctx Γ.
Proof.
  induction 1; eauto. econstructor.
Qed.

Lemma open_preserves_pty_measure ρ k t:
  pty_measure ρ = pty_measure ({k ~p> t} ρ)
with open_preserves_hty_measure τ k t:
  hty_measure τ = hty_measure ({k ~h> t} τ).
Proof.
  destruct ρ; simpl; eauto.
  destruct τ; simpl; eauto.
Qed.

Lemma subst_preserves_pty_measure ρ x t:
  pty_measure ρ = pty_measure ({x:=t}p ρ)
with subst_preserves_hty_measure τ x t:
  hty_measure τ = hty_measure ({x:=t}h τ).
Proof.
  destruct ρ; simpl; eauto.
  destruct τ; simpl; eauto.
Qed.

(* The conclusion has to be strengthened to an equivalence to get around
termination checker. *)
Lemma ptyR_measure_irrelevant m n ρ e :
  pty_measure ρ <= n ->
  pty_measure ρ <= m ->
  ptyR n ρ e <-> ptyR m ρ e
with htyR_measure_irrelevant m n τ e :
  hty_measure τ <= n ->
  hty_measure τ <= m ->
  htyR n τ e <-> htyR m τ e.
Proof.
  all: destruct m, n; intros;
    try solve [ pose proof (pty_measure_gt_0 ρ); lia
              | pose proof (hty_measure_gt_0 τ); lia ];
    specialize (ptyR_measure_irrelevant m);
    specialize (htyR_measure_irrelevant m);
    simpl.
  - intuition.
    + destruct ρ; intros; simpl in *; eauto.
      rewrite <- htyR_measure_irrelevant.
      auto_apply.
      rewrite ptyR_measure_irrelevant; eauto. lia. lia.
      rewrite <- open_preserves_hty_measure. lia.
      rewrite <- open_preserves_hty_measure. lia.
      rewrite <- ptyR_measure_irrelevant; eauto.
      rewrite <- open_preserves_pty_measure. lia.
      rewrite <- open_preserves_pty_measure. lia.
    + destruct ρ; intros; simpl in *; eauto.
      rewrite htyR_measure_irrelevant.
      auto_apply.
      rewrite <- ptyR_measure_irrelevant; eauto. lia. lia.
      rewrite <- open_preserves_hty_measure. lia.
      rewrite <- open_preserves_hty_measure. lia.
      rewrite ptyR_measure_irrelevant; eauto.
      rewrite <- open_preserves_pty_measure. lia.
      rewrite <- open_preserves_pty_measure. lia.
  - intuition.
    + destruct τ; intros; simpl in *; eauto.
      specialize (H4 _ _ _ H3 H5). intuition.
      rewrite <- ptyR_measure_irrelevant; eauto. lia. lia.
      intuition.
      rewrite <- htyR_measure_irrelevant; eauto. lia. lia.
      rewrite <- htyR_measure_irrelevant; eauto. lia. lia.
    + destruct τ; intros; simpl in *; eauto.
      specialize (H4 _ _ _ H3 H5). intuition.
      rewrite ptyR_measure_irrelevant; eauto. lia. lia.
      intuition.
      rewrite htyR_measure_irrelevant; eauto. lia. lia.
      rewrite htyR_measure_irrelevant; eauto. lia. lia.
Qed.

Lemma ptyR_measure_irrelevant' n ρ e :
  pty_measure ρ <= n ->
  ptyR n ρ e <-> p⟦ ρ ⟧ e.
Proof.
  intros. rewrite ptyR_measure_irrelevant; eauto.
Qed.

Lemma htyR_measure_irrelevant' n τ e :
  hty_measure τ <= n ->
  htyR n τ e <-> ⟦ τ ⟧ e.
Proof.
  intros. rewrite htyR_measure_irrelevant; eauto.
Qed.

Definition tm_refine e e' :=
  (* Alternatively, we may require [∅ ⊢t e ⋮t ⌊τ⌋] in [htyR_refine]. However, we
  would need [wf_hty] as a side-condition (or some sort of validity of [hty]),
  to make sure all components in intersection have the same erasure. This would
  introduce a large set of naming lemmas about [wf_hty] (and consequently
  everything it depends on). Annoying. *)
  (forall T, ∅ ⊢t e' ⋮t T -> ∅ ⊢t e ⋮t T) /\
  (forall α β (v : value), α ⊧ e ↪*{ β} v -> α ⊧ e' ↪*{ β} v).

Lemma htyR_refine τ e1 e2 :
  tm_refine e2 e1 ->
  ⟦ τ ⟧ e1 ->
  ⟦ τ ⟧ e2.
Proof.
  intros [Ht Hr].
  assert (hty_measure τ <= hty_measure τ) by reflexivity.
  revert H. generalize (hty_measure τ) at 2 3 4 as n.
  intros n. revert Ht. revert τ.
  induction n. easy.
  simpl. intuition.
  destruct τ; eauto.
  simpl in *. intuition.
  apply IHn; eauto. lia.
  apply IHn; eauto. lia.
Qed.
