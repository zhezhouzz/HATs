From stdpp Require Import mapset.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.

(** the step-indexed small step operational semantics *)
Inductive multistep_length : tm -> tm -> nat -> Prop :=
| multistep_length_refl : forall (x : tm),
    lc x ->
    multistep_length x x 0
| multistep_length_step : forall (x y z : tm) n,
    step x y ->
    multistep_length y z n ->
    multistep_length x z (S n).

Notation "t1 '↪{' n '}' t2" := (multistep_length t1 t2 n) (at level 40).

Lemma multistep_has_length: forall (e e': tm), e ↪* e' <-> (exists n, e ↪{n} e').
Proof.
  split; intros.
  - induction H.
    + exists 0. constructor; auto.
    + destruct IHmultistep as (n & Hn). exists (S n). econstructor; eauto.
  - destruct H as (n & Hn). generalize dependent e. generalize dependent e'.
    induction n; intros; inversion Hn; subst.
    + constructor; auto.
    + eapply multistep_step; eauto.
Qed.

Lemma multi_step_length_regular: forall e1 e2 n, e1 ↪{n} e2 -> lc e1 /\ lc e2.
Proof.
  intros.
  apply multi_step_regular. rewrite multistep_has_length. eexists; eauto.
Qed.

Ltac step_length_regular_simp1 :=
  repeat match goal with
    | [H: _ ↪ _ |- lc _] => apply step_regular in H; destruct H; auto
    | [H: _ ↪ _ |- body _] => apply step_regular in H; destruct H; auto
    | [H: _ ↪* _ |- lc _] => apply multi_step_regular in H; destruct H; auto
    | [H: _ ↪* _ |- body _] => apply multi_step_regular in H; destruct H; auto
    | [H: _ ↪{_} _ |- lc _] => apply multi_step_length_regular in H; destruct H; auto
    | [H: _ ↪{_} _ |- body _] => apply multi_step_length_regular in H; destruct H; auto
    | [H: ?a ↪{_} ?b |- ?a ↪* ?b] => rewrite multistep_has_length; eexists; eauto
    end.

Ltac step_length_regular_solver1 :=
  step_length_regular_simp1; lc_solver.

Theorem multistep_length_R : forall (x y : tm),
    step x y -> multistep_length x y 1.
Proof.
  intros x y H.
  apply multistep_length_step with y. apply H. apply multistep_length_refl; eauto.
Qed.

Theorem multistep_length_trans :
  forall (x y z : tm) n1 n2,
      multistep_length x y n1 ->
      multistep_length y z n2 ->
      multistep_length x z (n1 + n2).
Proof.
  intros.
  induction H.
    - simpl. assumption.
    - rewrite PeanoNat.Nat.add_succ_l. econstructor; eauto.
Qed.

Lemma multi_ruduction_lete: forall n e_x e_x' e, body e -> e_x ↪{n} e_x' -> (tlete e_x e) ↪{n} (tlete e_x' e).
Proof.
  induction n; intros; invclear H0.
  - constructor. lc_solver.
  - econstructor; eauto.
    econstructor; eauto.
Qed.

Lemma lete_reduction_spec_forward: forall n (e_x: tm) e (v: value),
    (tlete e_x e ↪{n} v -> exists (v_x: value) n1 n2, n = S (n1 + n2) /\ e_x ↪{n1} v_x /\ e ^t^ v_x ↪{n2} v).
Proof.
  induction n; intros; invclear H.
  - invclear H1.
    + apply IHn in H4. destruct H4 as (v_x & n1 & n2 & HH). repeat destruct_hyp_conj.
      exists v_x, (S n1), n2. repeat split; auto. econstructor; eauto.
    + exists v1, 0, n. intros. repeat split; auto. constructor; auto.
Qed.

Lemma lete_reduction_spec_backward: forall n (e_x: tm) e (v: value),
    (body e /\ exists (v_x: value) n1 n2, n = S (n1 + n2) /\ e_x ↪{n1} v_x /\ e ^t^ v_x ↪{n2} v) -> tlete e_x e ↪{n} v.
Proof.
  intros. repeat destruct_hyp_conj; subst.
  assert (S (x0 + x1) = (x0 + S x1)) as Htmp by lia. rewrite Htmp. clear Htmp.
  apply multistep_length_trans with (tlete x e). apply multi_ruduction_lete; eauto.
  econstructor; eauto.
  econstructor; eauto; step_length_regular_simp1.
Qed.

Lemma lete_reduction_spec: forall n (e_x: tm) e (v: value),
    (tlete e_x e ↪{n} v <-> body e /\ exists (v_x: value) n1 n2, n = S (n1 + n2) /\ e_x ↪{n1} v_x /\ e ^t^ v_x ↪{n2} v).
Proof.
  split.
  - split.
    + step_length_regular_solver1.
    + apply lete_reduction_spec_forward; auto.
  - apply lete_reduction_spec_backward.
Qed.

Lemma letbiop_reduction_spec_aux: forall op (v1 v2 : value) e e',
    tletbiop op v1 v2 e ↪ e' -> (exists (n1 n2: nat), v1 = n1 /\ v2 = n2).
Proof.
  intros.
  invclear H. destruct op; invclear H6; eexists; eauto.
Qed.

Lemma letbiop_reduction_spec: forall n op (v1 v2 : value) (v : value) e,
    tletbiop op v1 v2 e ↪{S n} v <->
      (exists (c1 c2: nat) (c: constant), v1 = c1 /\ v2 = c2 /\ body e /\ eval_op op c1 c2 c /\ e ^t^ c ↪{n} v).
Proof.
  split; intros.
  - invclear H.
    assert ((exists (n1 n2: nat), v1 = n1 /\ v2 = n2)) as Htmp by (eapply letbiop_reduction_spec_aux; eauto).
    mydestr; subst. invclear H1.
    exists x, x0, c3. repeat split; auto.
  - mydestr; subst. econstructor; eauto. econstructor; eauto; lc_solver.
Qed.

Lemma letapp_reduction_spec_aux: forall (v1 v2 : value) e e',
    tletapp v1 v2 e ↪ e' -> (exists T e1, v1 = vlam T e1) \/ (exists T (v1': value), v1 = vfix T v1').
Proof.
  intros.
  invclear H.
  - left. eexists; eauto.
  - right. eexists; eauto.
Qed.

Lemma letapp_reduction_spec: forall n (v1 v2 : value) (v : value) e,
    tletapp v1 v2 e ↪{n} v <->
      exists n', n = S n' /\ lc v1 /\ lc v2 /\ body e /\
              ((exists T e1,  v1 = vlam T e1 /\ (tlete (e1 ^t^ v2) e) ↪{n'} v) \/
                 (exists T Tx (e1: tm), v1 = vfix T (vlam Tx e1) /\
                                        (tletapp ((vlam T e1) ^v^ v2) (vfix T (vlam Tx e1)) e) ↪{n'} v)).
Proof.
  split; intros.
  - destruct n. inversion H.
    exists n. repeat split; auto; step_length_regular_solver1. invclear H.
    destruct (letapp_reduction_spec_aux v1 v2 _ _ H1); repeat destruct_hyp_conj; subst; invclear H1.
    + left. repeat eexists; eauto.
    + right. repeat eexists; eauto.
  - repeat destruct_hyp_conj; subst.
    destruct H3; repeat destruct_hyp_conj; subst.
    + econstructor; eauto. econstructor; eauto; lc_solver.
    + econstructor; eauto. econstructor; eauto. rewrite body_vlam_eq.
      instantiate (1:=x1). lc_solver.
Qed.

Lemma multistep_lete: forall e_x e_x' e, body e -> e_x ↪* e_x' -> (tlete e_x e) ↪* (tlete e_x' e).
Proof.
  intros. rewrite multistep_has_length in H0. rewrite multistep_has_length.
  mydestr. eexists.
  eapply multi_ruduction_lete; eauto.
Qed.

Lemma lete_step_spec: forall (e_x: tm) e (v: value),
    (tlete e_x e ↪* v <-> body e /\ exists (v_x: value), e_x ↪* v_x /\ e ^t^ v_x ↪* v).
Proof.
  split; intros.
  - split. step_length_regular_solver1.
    rewrite multistep_has_length in H. mydestr. rewrite lete_reduction_spec in H. mydestr; subst.
    eexists. split; rewrite multistep_has_length; eauto.
  - mydestr. rewrite multistep_has_length.
    rewrite multistep_has_length in H0.
    rewrite multistep_has_length in H1.
    mydestr.
    exists (S (x1 + x0)). rewrite lete_reduction_spec. split; auto.
    repeat eexists; repeat split; eauto.
Qed.

Lemma letapp_step_spec: forall (v1 v2: value) e (v: value),
    tletapp v1 v2 e ↪* v <->
       lc v1 /\ lc v2 /\ body e /\
         ((exists T e1, v1 = vlam T e1 /\ (tlete (e1 ^t^ v2) e) ↪* v) \/
                 (exists T Tx (e1: tm), v1 = vfix T (vlam Tx e1) /\
                                        (tletapp ((vlam T e1) ^v^ v2) (vfix T (vlam Tx e1)) e) ↪* v)).
Proof.
  split; intros.
  - repeat split; step_length_regular_solver1.
    rewrite multistep_has_length in H. mydestr. rewrite letapp_reduction_spec in H. mydestr; subst.
    destruct_hyp_disj; mydestr; subst.
    + left. repeat eexists; repeat split; eauto. step_length_regular_solver1.
    + right. repeat eexists; repeat split; eauto. step_length_regular_solver1.
  - mydestr.
    destruct_hyp_disj; mydestr; subst; econstructor; eauto.
    + econstructor; eauto. step_length_regular_solver1.
    + econstructor; eauto. rewrite body_vlam_eq. instantiate (1:=x0). step_length_regular_solver1.
Qed.

Lemma letbiop_step_spec: forall op (v1 v2 : value) (v : value) e,
    tletbiop op v1 v2 e ↪* v <->
      (exists (c1 c2: nat) (c: constant), v1 = c1 /\ v2 = c2 /\ body e /\ eval_op op c1 c2 c /\ e ^t^ c ↪* v).
Proof.
  split; intros.
  - invclear H.
    assert ((exists (n1 n2: nat), v1 = n1 /\ v2 = n2)) as Htmp by (eapply letbiop_reduction_spec_aux; eauto).
    mydestr; subst. invclear H0. exists x, x0, c3. repeat split; auto.
  - mydestr; subst. econstructor; eauto. econstructor; eauto.
Qed.

Lemma terr_reduction_exfalso1: forall (v: value), ~ terr ↪* v.
Proof.
  intros. intro Hf. invclear Hf.
  - inversion H.
Qed.

Ltac auto_reduction_exfalso1 :=
  match goal with
  | [H: ?P, H': ~ ?P |- _ ] => apply H' in H; inversion H
  | [H: terr ↪ _ |- _ ] => inversion H
  | [H: terr ↪* (tvalue _) |- _ ] => apply terr_reduction_exfalso1 in H; inversion H
  end.

Lemma tlete_terr_not_reduce_to_value: forall e (v: value), ~ tlete e terr ↪* v.
Proof.
  intros. intro Hf. rewrite lete_step_spec in Hf; mydestr. simpl in H1. auto_reduction_exfalso1.
Qed.

Ltac auto_reduction_exfalso2 :=
  match goal with
  | [H: tlete _ terr ↪* (tvalue _) |- _ ] => apply tlete_terr_not_reduce_to_value in H; invclear H
  end || auto_reduction_exfalso1.

Ltac auto_reduction_exfalso := auto_reduction_exfalso2.
