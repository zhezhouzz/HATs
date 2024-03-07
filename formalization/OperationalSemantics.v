From stdpp Require Import mapset.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
From CT Require Import Trace.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

(** This file defines the operational semantics of the core language. *)

Reserved Notation "α '⊧' t1 '↪{' β '}' t2" (at level 60, t1 constr, β constr).

(** the small step operational semantics (Fig. 3) *)
(* Because in this formalization, we treat pure operations as effectful
operations, the rule [STPureOp] is not necessary. *)
Inductive step : list evop -> tm -> list evop -> tm -> Prop :=
| STEffOp: forall (α: list evop) op (c1 c: constant) e,
    body e -> lc c1 -> lc c ->
    α ⊧{ op ~ c1 }⇓{ c } ->
    α ⊧ (tleteffop op c1 e) ↪{ [ev{ op ~ c1 := c}] } (e ^t^ c)
| STLetE1: forall α β e1 e1' e,
    body e ->
    α ⊧ e1 ↪{β} e1' ->
    α ⊧ (tlete e1 e) ↪{β} (tlete e1' e)
| STLetE2: forall α (v1: value) e,
    lc v1 -> body e ->
    α ⊧ (tlete (treturn v1) e) ↪{ [] } (e ^t^ v1)
| STLetAppLam: forall α T (v_x: value) e1 e,
    body e1 -> body e -> lc v_x ->
    α ⊧ (tletapp (vlam T e1) v_x e) ↪{ [] } tlete (e1 ^t^ v_x) e
| STLetAppFix: forall α T_f (v_x: value) (e1: tm) e,
    body (vlam T_f e1) -> lc v_x -> body e ->
    α ⊧ tletapp (vfix T_f (vlam T_f e1)) v_x e ↪{ [] }
            tletapp ((vlam T_f e1) ^v^ v_x) (vfix T_f (vlam T_f e1)) e
| STMatchbTrue: forall α e1 e2,
    lc e1 -> lc e2 ->
    α ⊧ (tmatchb true e1 e2) ↪{ [] } e1
| STMatchbFalse: forall α e1 e2,
    lc e1 -> lc e2 ->
    α ⊧ (tmatchb false e1 e2) ↪{ [] } e2
where "α '⊧' t1 '↪{' β '}' t2" := (step α t1 β t2).
  
Inductive multistep : list evop -> tm -> list evop -> tm -> Prop :=
| multistep_refl : forall α (e : tm),
    lc e -> multistep α e [] e
| multistep_step : forall  α β β' (x y z: tm),
    α ⊧ x ↪{ β } y ->
    multistep (α ++ β) y β' z ->
    multistep α x (β ++ β') z.

Notation "α '⊧' t1 '↪*{' β '}' t2" := (multistep α t1 β t2) (at level 60, t1 constr, β constr).

Definition pure_multistep (t1 t2: tm) := forall α, α ⊧ t1 ↪*{ [] } t2.

Notation "t1 '↪*' t2" := (pure_multistep t1 t2) (at level 60, t1 constr, t2 constr).

Global Hint Constructors multistep : core.

(** * Properties of operational semantics *)

Lemma step_regular: forall α β e1 e2, α ⊧ e1 ↪{ β } e2 -> lc e1 /\ lc e2.
Proof.
  intros.
  induction H; split; auto.
  - destruct H. econstructor; auto. apply H.
  - apply open_lc_tm; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - try destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - apply open_lc_tm; auto.
  - rewrite letapp_lc_body; split; auto. rewrite lc_abs_iff_body; auto.
  - rewrite lete_lc_body; split; auto. apply open_lc_tm; auto.
  - rewrite letapp_lc_body; split; auto. rewrite lc_fix_iff_body; auto.
  - rewrite letapp_lc_body; split; auto.
    + eapply open_lc_value; eauto.
    + rewrite body_vlam_eq in H. rewrite lc_fix_iff_body; eauto.
Qed.

Lemma step_regular1: forall α β e1 e2, α ⊧ e1 ↪{ β } e2 -> lc e1.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Lemma step_regular2: forall α β e1 e2, α ⊧ e1 ↪{ β } e2 -> lc e2.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Global Hint Resolve step_regular1: core.
Global Hint Resolve step_regular2: core.

Theorem multistep_trans :
  forall α βx βy (x y z : tm),
   α ⊧ x ↪*{ βx } y ->
   (α ++ βx) ⊧ y ↪*{ βy } z ->
   α ⊧ x ↪*{ βx ++ βy } z.
Proof.
  intros. generalize dependent z.
  induction H; intros.
  - simpl. rewrite app_nil_r in H0. eauto.
  - rewrite <- app_assoc.
    apply multistep_step with y; auto. apply IHmultistep.
    rewrite <- app_assoc; auto.
Qed.

Theorem multistep_R : forall α β (x y : tm),
    α ⊧ x ↪{ β } y -> α ⊧ x ↪*{ β } y.
Proof. intros.
  setoid_rewrite <- app_nil_r at 2. eauto.
Qed.

Lemma multi_step_regular: forall α β e1 e2, α ⊧ e1 ↪*{ β } e2 -> lc e1 /\ lc e2.
Proof.
  induction 1; intuition eauto.
Qed.

Lemma multi_step_regular1: forall α β e1 e2, α ⊧ e1 ↪*{ β } e2 -> lc e1.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Lemma multi_step_regular2: forall α β e1 e2, α ⊧ e1 ↪*{ β } e2 ->  lc e2.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Ltac step_regular_simp :=
  repeat match goal with
    | [H: _ ⊧ _ ↪*{ _ } _ |- lc _ ] => apply multi_step_regular in H; destruct H; auto
    | [H: _ ⊧ _ ↪{ _ } _ |- lc _ ] => apply step_regular in H; destruct H; auto
    | [H: _ ⊧ _ ↪*{ _ } _ |- body _] => apply multi_step_regular in H; destruct H; auto
    | [H: _ ⊧ _ ↪{ _ } _ |- body _] => apply step_regular in H; destruct H; auto
    end.

Lemma value_reduction_refl: forall α β (v1: value) v2, α ⊧ v1 ↪*{ β} v2 -> v2 = v1 /\ β = [].
Proof.
  intros * H.
  sinvert H; easy.
Qed.

Ltac reduction_simp :=
  match goal with
  | H: _ ⊧ (treturn _) ↪*{ _ } _  |- _ =>
      apply value_reduction_refl in H; simp_hyps; simplify_eq
  end.

Lemma reduction_tlete:  forall e_x e α β (v : value),
    α ⊧ tlete e_x e ↪*{ β } v ->
    (exists (βx βe: trace) (v_x: value),
      β = βx ++ βe /\ α ⊧ e_x ↪*{ βx } v_x /\ (α ++ βx) ⊧ (e ^t^ v_x) ↪*{ βe } v).
Proof.
  intros.
  remember (tlete e_x e). remember (treturn v).
  generalize dependent e_x.
  induction H; intros; subst. easy.
  sinvert H.
  - ospecialize* IHmultistep; eauto.
    simp_hyps.
    eexists _, _, _. split; [ | split ]; cycle 1.
    econstructor; eauto. simplify_list_eq. eauto.
    simplify_list_eq. eauto.
  - repeat esplit. econstructor; eauto. eauto.
Qed.

Lemma reduction_tlete':  forall e_x e α βx βe (v_x v : value),
    (* NOTE: This condition is unnecessary as it should be implied by the
    regularity lemma. Remove later when we bother proving a few more naming
    lemmas. *)
    body e ->
    α ⊧ e_x ↪*{ βx } v_x ->
    (α ++ βx) ⊧ (e ^t^ v_x) ↪*{ βe } v ->
    α ⊧ tlete e_x e ↪*{ βx ++ βe } v.
Proof.
  intros * Hb H. remember (treturn v_x).
  induction H; intros; subst.
  - econstructor; eauto using STLetE2.
  - simp_hyps.
    simplify_list_eq.
    econstructor.
    econstructor; eauto.
    eauto.
Qed.

Lemma reduction_mk_app_e_v α β (f v_x v : value) :
  lc v_x ->
  α ⊧ mk_app_e_v f v_x ↪*{ β} v ->
  α ⊧ tletapp f v_x (vbvar 0) ↪*{ β} v.
Proof.
  intros Hlc H.
  sinvert H. sinvert H0. easy.
  simpl in *. simplify_list_eq.
  rewrite open_rec_lc_value in * by eauto. eauto.
Qed.

Lemma reduction_mk_app_e_v' α β (f v_x v : value) :
  α ⊧ tletapp f v_x (vbvar 0) ↪*{ β} v ->
  α ⊧ mk_app_e_v f v_x ↪*{ β} v.
Proof.
  intros H.
  assert (lc v_x). {
    apply multi_step_regular1 in H. sinvert H. eauto.
  }
  eapply_eq multistep_step.
  eapply STLetE2.
  apply multi_step_regular1 in H. sinvert H. eauto.
  (* Probably should be a lemma. *)
  eexists. instantiate_atom_listctx.
  simpl. apply letapp_lc_body. repeat split; eauto using lc.
  by rewrite open_rec_lc_value.
  simpl. simplify_list_eq. rewrite open_rec_lc_value; eauto.
  eauto.
Qed.

Lemma reduction_letapplam α Tb e (v_x : value) β (v : value) :
  lc v_x ->
  α ⊧ mk_app_e_v (vlam Tb e) v_x ↪*{ β} v ->
  α ⊧ e ^t^ v_x ↪*{ β} v.
Proof.
  intros Hlc H.
  sinvert H.
  sinvert H0; try easy.
  simpl in H1.
  rewrite open_rec_lc_value in H1 by auto.
  sinvert H1. sinvert H.
  apply reduction_tlete in H0.
  simp_hyps. simpl in *.
  sinvert H2; try easy.
  simplify_list_eq; eauto.
Qed.

Lemma reduction_letapplam' α Tb e (v_x : value) β (v : value) :
  lc v_x ->
  (* NOTE: This condition is unnecessary as it should be implied by the
  regularity lemma. *)
  body e ->
  α ⊧ e ^t^ v_x ↪*{ β} v ->
  α ⊧ mk_app_e_v (vlam Tb e) v_x ↪*{ β} v.
Proof.
  intros Hlc Hb H.
  eapply_eq multistep_step.
  eapply STLetE2.
  qauto using lc_abs_iff_body.
  (* probably should be a lemma. *)
  eexists. instantiate_atom_listctx.
  simpl. apply letapp_lc_body. repeat split; eauto using lc.
  by rewrite open_rec_lc_value.
  simpl. econstructor.
  econstructor. eauto. eauto.
  by rewrite open_rec_lc_value.
  rewrite open_rec_lc_value by eauto.
  simplify_list_eq. eapply reduction_tlete'; eauto.
  simpl. econstructor. eauto using multi_step_regular2.
  simplify_list_eq. auto.
Qed.

Lemma reduction_tletapp:  forall v1 v2 e α β (v : value),
    α ⊧ tletapp v1 v2 e ↪*{ β} v ->
    (exists (βx βe: trace) (v_x: value),
      β = βx ++ βe /\ α ⊧ mk_app_e_v v1 v2 ↪*{ βx } v_x /\
        (α ++ βx) ⊧ (e ^t^ v_x) ↪*{ βe } v).
Proof.
  intros.
  remember (tletapp v1 v2 e). remember (treturn v).
  generalize dependent v2.
  generalize dependent v1.
  induction H; intros; subst. easy.
  simp_hyps. sinvert H.
  - eapply reduction_tlete in H0. simp_hyps.
    simplify_list_eq.
    eexists _, _, _. split; [| split]; eauto using reduction_letapplam'.
  - simplify_list_eq.
    ospecialize* H1; eauto. simp_hyps.
    eexists _, _, _.
    repeat split; cycle 1.

    (* Maybe this should be a lemma about [vfix]. *)
    apply reduction_mk_app_e_v in H.
    apply reduction_mk_app_e_v'.
    econstructor. econstructor; eauto.
    simplify_list_eq. eauto.
    apply multi_step_regular1 in H0.
    sinvert H0. eauto.

    simplify_list_eq. eauto.
    simplify_list_eq. eauto.
Qed.

Lemma reduction_tleteffop:  forall op v2 e α β (v : value),
    α ⊧ (tleteffop op v2 e) ↪*{ β} v ->
    exists (c2 c_x: constant) β',
      v2 = c2 /\ β = ev{ op ~ c2 := c_x } :: β' /\
        α ⊧{op ~ c2}⇓{ c_x } /\ (α ++ [ev{op ~ c2 := c_x}]) ⊧ (e ^t^ c_x) ↪*{ β'} v .
Proof.
  intros.
  sinvert H. sinvert H0.
  eauto 10.
Qed.

Lemma reduction_matchb_true:  forall e1 e2 α β (v : value),
    α ⊧ tmatchb true e1 e2 ↪*{ β} v -> α ⊧ e1 ↪*{ β} v.
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.

Lemma reduction_matchb_false:  forall e1 e2 α β (v : value),
    α ⊧ tmatchb false e1 e2 ↪*{ β} v -> α ⊧ e2 ↪*{ β} v.
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.
