From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.
From CT Require Import RefinementType.
From CT Require Import RefinementTypeTac.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import OperationalSemanticsProp.
Import BasicTyping.
Import SyntaxSugar.
Import RefinementType.
Import RefinementTypeTac.

(** Type Denotation: *)
Fixpoint rR (n: nat) (bst: bstate) (st: state) (τ: rty) (e: tm) : Prop :=
  [] ⊢t e ⋮t ⌊ τ ⌋ /\ closed_rty n (dom _ st) τ /\
    match τ with
    | {v: B | _ | _ | ϕ} => exists (c: constant), [] ⊢t c ⋮v B /\ ϕ bst st c /\ e = c
    | [v: B | _ | _ | ϕ] => forall (c: constant), [] ⊢t c ⋮v B -> ϕ bst st c -> e ↪* c
    | -:{v: B | _ | d | ϕ } ⤑ τ =>
        exists (v: value), e ↪* v /\
                        forall (c_x: constant),
                          [] ⊢t c_x ⋮v B -> ϕ bst st c_x -> rR (S n) (<b[↦ c_x ]> bst) st τ (mk_app v c_x)
    | τ1 ⤑ τ2 =>
        exists (v: value), e ↪* v /\
                        (forall (v_x: value), rR n bst st τ1 v_x -> rR n bst st τ2 (mk_app v v_x))
    end.

Lemma bst_eq_trans: forall n n' (bst1 bst2: bstate), n' <= n -> bst_eq n bst1 bst2 -> bst_eq n' bst1 bst2.
Proof.
  intros. intro i; intros. apply H0. lia.
Qed.

Lemma closed_rty_n_overbase: forall (n1 n2: nat) d1 d2 B ϕ, closed_rty n1 d1 {v:B|n2|d2|ϕ} -> n2 <= n1.
Proof.
  intros. invclear H; mydestr. invclear H0. invclear H1; auto.
Qed.

Lemma closed_rty_n_underbase: forall (n1 n2: nat) d1 d2 B ϕ, closed_rty n1 d1 [v:B|n2|d2|ϕ] -> n2 <= n1.
Proof.
  intros. invclear H; mydestr. invclear H0. invclear H1; auto.
Qed.

Lemma closed_rty_0_overbase: forall (n2: nat) d1 d2 B ϕ, closed_rty 0 d1 {v:B|n2|d2|ϕ} -> n2 = 0.
Proof.
  intros. apply closed_rty_n_overbase in H. lia.
Qed.

Lemma closed_rty_0_underbase: forall (n2: nat) d1 d2 B ϕ, closed_rty 0 d1 [v:B|n2|d2|ϕ] -> n2 = 0.
Proof.
  intros. apply closed_rty_n_underbase in H. lia.
Qed.

Lemma bst_eq_symmetry: forall n bst1 bst2, bst_eq n bst2 bst1 <-> bst_eq n bst1 bst2.
Proof.
  unfold bst_eq. split; intros; rewrite H; auto.
Qed.

Lemma bst_eq_push: forall n c_x bst1 bst2, bst_eq n bst1 bst2 -> bst_eq  (S n) (<b[↦c_x]> bst1) (<b[↦c_x]> bst2).
Proof.
  intros. intro i; intros.
  destruct i; simpl; auto. apply H. lia.
Qed.

Lemma rR_bst_bound_: forall τ (e: tm) st n (bst1 bst2: bstate), bst_eq n bst1 bst2 -> rR n bst1 st τ e -> rR n bst2 st τ e.
Proof.
  induction τ; intros; auto; invclear H0; mydestr; subst.
  - constructor; auto. constructor; auto. exists x. repeat split; auto.
    invclear H0; mydestr. invclear H4. invclear H7. invclear H5. eapply H4; eauto.
    rewrite bst_eq_symmetry in H. eapply bst_eq_trans; eauto.
  - constructor; auto. constructor; auto. intros. apply H2; auto.
    invclear H0; mydestr. invclear H5. invclear H8. invclear H6. eapply H5; eauto. eapply bst_eq_trans; eauto.
  - constructor; auto. constructor; auto.
    eexists; split; eauto.
    intros.
    apply IHτ with (bst1 := (<b[↦c_x]> bst1)). apply bst_eq_push; auto. apply H3; auto.
    invclear H0; mydestr. invclear H6. invclear H11. eapply H6; eauto. invclear H7. eapply bst_eq_trans; eauto.
  - constructor; auto. constructor; auto. eexists; split; eauto. intros.
    eapply IHτ2; eauto. apply H3; auto.
    eapply IHτ1; eauto. rewrite bst_eq_symmetry; auto.
Qed.

Lemma rR_bst_bound: forall τ (e: tm) st n (bst1 bst2: bstate), bst_eq n bst1 bst2 -> rR n bst1 st τ e <-> rR n bst2 st τ e.
Proof.
  split; intros; eapply rR_bst_bound_; eauto. rewrite bst_eq_symmetry; eauto.
Qed.

Lemma rR_0_empty_iff_forall: forall τ (e: tm) st, (forall bst1, rR 0 bst1 st τ e) <-> rR 0 b∅ st τ e.
Proof.
  split; intros; auto. rewrite rR_bst_bound; eauto. intro i; intros. invclear H0.
Qed.

Notation " '{' n ';' bst ';' st '}⟦' τ '⟧' " :=
  (rR n bst st τ) (at level 20, format "{ n ; bst ; st }⟦ τ ⟧", bst constr, st constr, τ constr).
Notation " '{' st '}⟦' τ '⟧' " := (fun e => rR 0 b∅ st τ e) (at level 20, format "{ st }⟦ τ ⟧", st constr, τ constr).
Notation " '⟦' τ '⟧' " := (fun e => rR 0 b∅ ∅ τ e) (at level 20, format "⟦ τ ⟧", τ constr).

Lemma rR_regular1:
  forall τ n bst st e, { n; bst; st }⟦ τ ⟧ e -> closed_rty n (dom _ st) τ /\ [] ⊢t e ⋮t ⌊ τ ⌋.
Proof.
  induction τ; intros; invclear H; mydestr; subst; split; intros; auto.
Qed.

Lemma rR_regular2:
  forall τ st e, { st }⟦ τ ⟧ e -> closed_rty 0 (dom _ st) τ /\ [] ⊢t e ⋮t ⌊ τ ⌋.
Proof.
  intros. eapply rR_regular1; eauto.
Qed.

Lemma rR_regular3:
  forall τ e, ⟦ τ ⟧ e -> (closed_rty 0 ∅ τ) /\ [] ⊢t e ⋮t ⌊ τ ⌋.
Proof.
  intros. eapply rR_regular2 in H. mydestr; split; auto.
  closed_rty_solver.
Qed.
