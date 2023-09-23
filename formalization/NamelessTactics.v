From stdpp Require Import mapset.
From CT Require Import Atom.
From CT Require Import Tactics.
From CT Require Import CoreLang.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.
From Coq Require Import Arith.Compare_dec.

Import CoreLang.

Ltac destruct_hyp_conj :=
  match goal with
  | [H: ?P /\ ?Q |- _ ] =>
      destruct H; repeat match goal with
                    | [ H' : P /\ Q |- _ ] => clear H'
                    end
  | [H: atom * _ |- _ ] => destruct H
  | [ H: ex _ |- _ ] => destruct H
  end.

Ltac destruct_hyp_disj :=
  repeat match goal with
    | [H: _ \/ _ |- _ ] => destruct H
    end.

Ltac mydestr := repeat destruct_hyp_conj.

Ltac invclear H := inversion H; subst; clear H.

Lemma setunion_cons_cons: forall (x: atom) (s1 s2: aset), {[x]} ∪ s1 ∪ ({[x]} ∪ s2) = ({[x]} ∪ s1 ∪ s2).
Proof. fast_set_solver. Qed.

Lemma setunion_empty_left: forall (s: aset), ∅ ∪ s = s.
Proof. fast_set_solver. Qed.

Lemma subseteq_substract_both: forall (x: atom) (s1 s2: aset), x ∉ s1 -> x ∉ s2 -> {[x]} ∪ s1 ⊆ {[x]} ∪ s2 -> s1 ⊆ s2.
Proof.
  intros.
  apply (difference_mono _ _ {[x]} {[x]}) in H1; auto.
  repeat rewrite difference_union_distr_l in H1.
  repeat rewrite difference_diag in H1.
  repeat rewrite setunion_empty_left in H1.
  rewrite difference_disjoint in H1.
  rewrite difference_disjoint in H1; fast_set_solver.
  fast_set_solver.
Qed.

Lemma setunion_cons_right: forall x (s2: aset), (s2 ∪ ({[x]} ∪ ∅)) = ({[x]} ∪ s2).
Proof. fast_set_solver. Qed.

Ltac mmy_set_simpl1 :=
  (repeat match goal with
     | [H: context [({[?x]} ∪ ?s ∪ ({[?x]} ∪ _))] |- _] => rewrite (setunion_cons_cons x s _) in H
     | [H: context [(?s2 ∪ ({[?x]} ∪ ∅))] |- _ ] => setoid_rewrite (setunion_cons_right x s2) in H
     end).

Lemma subseteq_substract_both': forall (x: atom) (s1 s2: aset), x ∉ s1 -> x ∉ s2 -> {[x]} ∪ s1 ⊆ s2 ∪ ({[x]} ∪ ∅) -> s1 ⊆ s2.
Proof.
  intros. mmy_set_simpl1.
  apply subseteq_substract_both in H1; auto.
Qed.

Ltac mmy_set_solver1 :=
  mmy_set_simpl1;
  match goal with
  | [H: ?s1 ∪ ?s2 ∪ ?s3 ⊆ ?s4 ∪ ?s5 ∪ ?s6 |- ?s1 ∪ (?s2 ∪ ?s3) ⊆ ?s4 ∪ (?s5 ∪ ?s6)] =>
      assert (forall (ss1 ss2 ss3: aset), ss1 ∪ (ss2 ∪ ss3) = (ss1 ∪ ss2 ∪ ss3)) as Htmp by fast_set_solver;
      do 2 rewrite Htmp; try clear Htmp; exact H
  | [H: {[?x]} ∪ ?s1 ⊆ {[?x]} ∪ ?s2 |- ?s1 ⊆ ?s2] => apply (subseteq_substract_both x); auto; fast_set_solver
  end.

Lemma setunion_mono_cons: forall (x: atom) (s1 s2 s3 s4: aset),
    {[x]} ∪ s1 ⊆ {[x]} ∪ s2 -> {[x]} ∪ s3 ⊆ {[x]} ∪ s4 -> {[x]} ∪ (s1 ∪ s3) ⊆ {[x]} ∪ (s2 ∪ s4).
Proof.
  intros.
  apply (union_mono ({[x]} ∪ s1) ({[x]} ∪ s2) ({[x]} ∪ s3) ({[x]} ∪ s4)) in H; auto.
   mmy_set_solver1.
Qed.

Ltac mmy_set_solver2 :=
  mmy_set_simpl1;
  match goal with
  | [ |- {[?x]} ∪ (?s1 ∪ ?s3) ⊆ {[?x]} ∪ (?s2 ∪ ?s4)] => apply setunion_mono_cons; auto
  | [H: ?s1 ∪ ?s2 ∪ ?s3 ⊆ ?s4 ∪ ?s5 ∪ ?s6 |- ?s1 ∪ (?s2 ∪ ?s3) ⊆ ?s4 ∪ (?s5 ∪ ?s6)] =>
      assert (forall (ss1 ss2 ss3: aset), ss1 ∪ (ss2 ∪ ss3) = (ss1 ∪ ss2 ∪ ss3)) as Htmp by fast_set_solver;
      do 2 rewrite Htmp; try clear Htmp; exact H
  end.

Ltac my_set_solver :=
  match goal with
  | [H: context [∅ ∪ ?d] |- _ ] =>
      assert (∅ ∪ d = d) as Htmp by fast_set_solver;
      rewrite Htmp in H; try clear Htmp; auto
  | [ |- context [∅ ∪ ?d] ] =>
      assert (∅ ∪ d = d) as Htmp by fast_set_solver;
      rewrite Htmp; try clear Htmp; auto
  end ||
    mmy_set_solver2 || fast_set_solver!! || set_solver.

Ltac rewrite_by_set_solver :=
  match goal with
  | H: context [ _ ->  _ = _ ]  |- _ => rewrite H by fast_set_solver!!
  end.

Ltac rewrite_by_fol :=
  match goal with
  | H: context [ _ ->  _ = _ ]  |- _ => rewrite H by firstorder
  end.

Ltac eempty_aset :=
  match goal with
  | [ |- context [_ -> True] ] => exists ∅; simpl; auto
  end.

Ltac bi_iff_rewrite :=
  match goal with
  | [ H: context [ _ <-> _ ] |- _ ] =>
      (rewrite <- H; firstorder; auto) || (rewrite H; firstorder; auto)
  end.

#[global]
Instance atom_stale : @Stale aset atom := singleton.
Arguments atom_stale /.
#[global]
Instance aset_stale : Stale aset := id.
Arguments aset_stale /.
#[global]
Instance value_stale : Stale value := fv_value.
Arguments value_stale /.
#[global]
Instance tm_stale : Stale tm := fv_tm.
Arguments tm_stale /.
Arguments stale /.

Ltac collect_one_stale e acc :=
  match goal with
  | _ =>
      lazymatch acc with
      | tt => constr:(stale e)
      | _ => constr:(acc ∪ stale e)
      end
  | _ => acc
  end.

(** Return all stales in the context. *)
Ltac collect_stales S :=
  let stales := fold_hyps S collect_one_stale in
  lazymatch stales with
  | tt => fail "no stale available"
  | _ => stales
  end.

Ltac lc_at_tm_rewrite :=
  repeat destruct_hyp_conj;
  match goal with
  | [H: forall k, _ _ ?e <-> ?Q, H': _ _ ?e |- _ ] =>
      rewrite H in H'; repeat destruct_hyp_conj; auto
  | [H: forall k, _ _ ?e <-> ?Q |- context [_ _ ?e] ] =>
      rewrite H; auto
  end.

Ltac apply_by_set_solver :=
  match goal with
  | [H: forall k, _ -> _ _ (_ _ _ ?e) |- _ _ (_ _ _ ?e) ] => apply H; auto; set_solver
  | [H: forall k, _ -> _ _ (_ _ ?e) |- _ _ (_ _ _ ?e) ] => simpl in H; apply H; auto; set_solver
  | [H: forall k, _ -> _ /\ _ |- _ _ (_ _ (vfvar ?x) ?e) ] =>
      specialize (H x); destruct H; auto; my_set_solver; auto
  end.

Ltac auto_exists_L :=
  let acc := collect_stales tt in econstructor; eauto; instantiate (1 := acc).

Ltac auto_exists_L_intros :=
let acc := collect_stales tt in instantiate (1 := acc); intros; simpl.

Ltac auto_exists_L_and_solve :=
  match goal with
  | [ |- ?P /\ _ ] => constructor; auto; auto_exists_L_and_solve
  | _ => auto_exists_L; intros; repeat split; apply_by_set_solver
  end.

Lemma empty_eq_app_exfalso {A: Type}: forall Γ1 (x: atom) (t: A) Γ2, ~ ([] = Γ1 ++ [(x, t)] ++ Γ2).
Proof.
  intros. intro H.
  symmetry in H. apply app_eq_nil in H. mydestr.
  apply app_eq_nil in H0. mydestr. inversion H0.
Qed.

Ltac auto_exfalso :=
  match goal with
  | [H: [] = _ ++ [(_, _)] ++ _ |- _] => apply empty_eq_app_exfalso in H; inversion H
  | [H: _ ++ [(_, _)] ++ _ = [] |- _] => symmetry in H; apply empty_eq_app_exfalso in H; inversion H
  | [H: ?a <> ?a |- _ ] => exfalso; auto
  | [H: False |- _] => inversion H
  | [H: Some _ = None |- _ ] => inversion H
  | [H: None = Some _ |- _ ] => inversion H
  | [H1: [] = _ ++ _ |- _ ] => symmetry in H1; apply app_eq_nil in H1; destruct H1 as (_ & H1); inversion H1
  end || (exfalso; fast_set_solver !!).

Ltac rw_decide_true a b :=
  assert (a = b) as Hrw_decide_true; auto; rewrite (decide_True _ _ Hrw_decide_true); clear Hrw_decide_true.

Ltac rw_decide_true_in a b H :=
  assert (a = b) as Hrw_decide_true; auto; rewrite (decide_True _ _ Hrw_decide_true) in H; clear Hrw_decide_true.

Ltac var_dec_solver :=
  try auto_exfalso;
  match goal with
  | [H: Some ?a = Some ?b |- _] => inversion H; subst; clear H; simpl; auto
  | [H: ?a <> ?a |- _ ] => exfalso; lia
  | [ |- Some _ = None ] => exfalso; lia
  | [ |- None = Some _ ] => exfalso; lia
  | [H: context [ decide (?a = ?a) ] |- _ ] => rw_decide_true_in a a H; auto
  | [H: context [ decide (?a = ?b) ] |- _ ] =>
      match goal with
      | [H': a = b |- _ ] => rw_decide_true_in a b H; auto
      | [H': a <> b |- _ ] => rewrite (decide_False _ _ H') in H; auto
      | _ => destruct (Nat.eq_dec a b); subst; simpl in H; simpl
      | _ => destruct (Atom.atom_dec a b); subst; simpl in H; simpl
      end
  | [H: context [ decide (?a < ?b) ] |- _ ] =>
      match goal with
      | [H': a < b |- _ ] => rewrite (decide_True _ _ H') in H; auto
      | [H': ~ (a < b) |- _ ] => rewrite (decide_False _ _ H') in H; auto
      | _ => destruct (lt_dec a b); subst; simpl in H; simpl
      end
  | [ |- context [ decide (?a = ?a) ] ] => rw_decide_true a a; auto
  | [ |- context [ decide (?a = ?b) ] ] =>
      match goal with
      | [H: a = b |- _ ] => rewrite (decide_True _ _ H); auto
      | [H: a <> b |- _ ] => rewrite (decide_False _ _ H); auto
      | _ => destruct (Nat.eq_dec a b); subst; simpl; var_dec_solver
      | _ => destruct (Atom.atom_dec a b); subst; simpl; var_dec_solver
      end
  | [ |- context [ decide (?a < ?b) ] ] =>
      match goal with
      | [H': a < b |- _ ] => rewrite (decide_True _ _ H'); auto
      | [H': ~ (a < b) |- _ ] => rewrite (decide_False _ _ H'); auto
      | _ => destruct (lt_dec a b); subst; simpl; simpl; var_dec_solver
      end
  | _ => progress simpl
  end.

Ltac auto_eq_post :=
  repeat match goal with
         | [ |- ?a ?e1 = ?a ?e2 ] =>
             assert (e1 = e2) as HH; try (rewrite HH; auto)
         | [|- ?a ?b ?e1 = ?a ?b ?e2 ] =>
             assert (e1 = e2) as HH; try (rewrite HH; auto)
         | [|- ?a ?b ?c ?e1 = ?a ?b ?c ?e2 ] =>
             assert (e1 = e2) as HH; try (rewrite HH; auto)
         | [ |- ?a ?b ?c1 = ?a ?b ?c2 ] =>
             assert (c1 = c2); auto
         | [ H: ?a _ = ?a _ |- _ ] =>
             inversion H; subst; clear H; auto
         | [ H: ?a _ _ = ?a _ _ |- _ ] =>
             inversion H; subst; clear H; auto
         | [ H: ?a _ _ _ = ?a _ _ _ |- _ ] =>
             inversion H; subst; clear H; auto
         end.

Ltac equate x y :=
  idtac x;
  let dummy := constr:(eq_refl x : x = y) in idtac.

Ltac specialize_with x :=
  match goal with
  | [H: forall x, x ∉ ?L -> _ |- _] =>
      let Htmp := fresh "Htmp" in
      assert (x ∉ L) as Htmp by fast_set_solver; specialize (H x Htmp); try clear Htmp
  end.

Ltac pbc :=
  match goal with
  | [ |- ?ret] => destruct (classic ret); auto; exfalso
  end.

Lemma exists_forall_aux2 {A: Type}: forall P Q, ~ (∃ (a: A), P a /\ Q a) <-> (∀ (a: A), ~ P a \/ ~ Q a).
Proof.
  split; intros.
  - destruct (classic (P a)); destruct (classic (Q a)); auto.
    exfalso. apply H. exists a. split; auto.
  - intro Hf. mydestr. destruct (H x).
    + apply H2; auto.
    + apply H2; auto.
Qed.

Lemma nexists {A: Type}: forall P, ~ (∃ (a: A), P a) <-> (forall (a: A), ~ P a).
Proof.
  split; intros.
  - intro Hf. apply H; eexists; eauto.
  - intro Hf; mydestr. eapply H; eauto.
Qed.

Lemma nand: forall P Q, ~ (P /\ Q) <-> (~ P \/ ~ Q).
Proof.
  split; intros.
  - destruct (classic P); destruct (classic Q); auto.
  - intro Hf; mydestr. destruct H; apply H; auto.
Qed.

Lemma nor_to_implies: forall P Q, (~ P \/ Q) <-> (P -> Q).
Proof.
  split; intros.
  - destruct H; auto. exfalso; apply H; auto.
  - destruct (classic P); auto.
Qed.

Lemma nneg: forall P, ~ ~ P <-> P.
Proof.
  split; intros.
  - destruct (classic P); auto. exfalso. apply H; auto.
  - intro Hf. apply Hf; auto.
Qed.

Ltac neg_simpl :=
  repeat match goal with
  | [H: ~ (exists _, _) |- _ ] => setoid_rewrite nexists in H
  | [H: context [ ~ (_ /\ _)] |- _ ] => setoid_rewrite nand in H
  | [H: context [ ~ ~ _ ] |- _ ] => setoid_rewrite nneg in H
  | [H: context [ ~ _ \/ _ ]  |- _ ] => setoid_rewrite nor_to_implies in H
  end.

Ltac neg_apply H := pbc; apply H; clear H; neg_simpl.

Ltac exfalso_apply H := exfalso; auto; eapply H; eauto.

Lemma forall_iff_not_exists1 {A: Type}: forall P: A -> Prop, ~ (exists x, P x) <-> forall x, ~ P x.
Proof.
  split; intros.
  - destruct (classic (P x)); auto. exfalso. apply H. exists x; auto.
  - intro Hf. mydestr. eapply H; eauto.
Qed.

From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.

(** Prop Extensionality *)
Lemma prop_ex3 {A B C: Type}: forall (P Q: A -> B -> C -> Prop), (forall a b c, P a b c <-> Q a b c) -> P = Q.
Proof.
  do 3 (intros; apply functional_extensionality).
  intros. apply propositional_extensionality. auto.
Qed.

Lemma subseteq_trans_cons: forall x (s1 s2 s3: aset), {[x]} ∪ s1 ⊆ {[x]} ∪ s2 -> s2 ⊆ {[x]} ∪ s3 -> {[x]} ∪ s1 ⊆ {[x]} ∪ s3.
Proof.
  intros.
  assert ({[x]} ∪ s2 ⊆ {[x]} ∪ s3). fast_set_solver.
  fast_set_solver.
Qed.

Ltac auto_pose_fv a :=
  let acc := collect_stales tt in
  pose (fv_of_set acc) as a;
  assert (a ∉ acc) by (apply fv_of_set_fresh; auto).

Ltac simpl_union H :=
  let rec go H :=
      lazymatch type of H with
      | _ ∉ _ ∪ _ =>
        rewrite not_elem_of_union in H;
          let H1 := fresh "Hfresh" in
          let H2 := fresh "Hfresh" in
          destruct H as [H1 H2]; go H1; go H2
      | _ => idtac
  end in go H.
