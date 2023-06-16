From stdpp Require Import mapset.
(* From Coq Require Import Logic.ClassicalFacts. *)
(* From Coq Require Import Classical. *)
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
From CT Require Import Trace.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

Reserved Notation "α '⊧' t1 '↪{' β '}' t2" (at level 60, t1 constr, β constr).

(** the small step operational semantics *)
Inductive step : list evop -> tm -> list evop -> tm -> Prop :=
| ST_LetEffOp: forall (α β: list evop) op (c1 c: constant) e,
    body e -> lc c1 -> lc c ->
    α ⊧{ op ~ c1 }⇓{ c } ->
    α ⊧ (tleteffop op c1 e) ↪{ [ev{ op ~ c1 := c}] } (e ^t^ c)
| ST_Lete1: forall α β e1 e1' e,
    body e ->
    α ⊧ e1 ↪{β} e1' ->
    α ⊧ (tlete e1 e) ↪{β} (tlete e1' e)
| ST_Lete2: forall α (v1: value) e,
    lc v1 -> body e ->
    α ⊧ (tlete (treturn v1) e) ↪{ [] } (e ^t^ v1)
| ST_LetAppLam: forall α T (v_x: value) e1 e,
    body e1 -> body e -> lc v_x ->
    α ⊧ (tletapp (vlam T e1) v_x e) ↪{ [] } tlete (e1 ^t^ v_x) e
| ST_LetAppFix: forall α T_f (v_x: value) Tx (e1: tm) e,
    body (vlam T_f e1) -> lc v_x -> body e ->
    α ⊧ tletapp (vfix T_f (vlam Tx e1)) v_x e ↪{ [] }
            tletapp ((vlam T_f e1) ^v^ v_x) (vfix T_f (vlam Tx e1)) e
| ST_Matchb_true: forall α e1 e2,
    lc e1 -> lc e2 ->
    α ⊧ (tmatchb true e1 e2) ↪{ [] } e1
| ST_Matchb_false: forall α e1 e2,
    lc e1 -> lc e2 ->
    α ⊧ (tmatchb false e1 e2) ↪{ [] } e2
where "α '⊧' t1 '↪{' β '}' t2" := (step α t1 β t2).

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
    rewrite body_vlam_eq; eauto.
  - rewrite letapp_lc_body; split; auto.
    + eapply open_lc_value; eauto.
    + split; auto. rewrite body_vlam_eq in H. rewrite lc_fix_iff_body; eauto.
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

(* Reserved Notation "α '⊧' t1 '↪*{' β '}' t2" (at level 60, t1 constr, β constr). *)

Inductive multistep : list evop -> tm -> list evop -> tm -> Prop :=
| multistep_refl : forall α (e : tm),
    lc e -> multistep α e [] e
(* | multistep_step : forall  α β β' (x y z: tm), *)
(*     multistep α x β y -> *)
(*     (α +;+ β) ⊧ y ↪{ β' } z -> *)
(*     multistep α x (β +;+ β') z. *)
| multistep_step : forall  α β β' (x y z: tm),
    α ⊧ x ↪{ β } y ->
    multistep (α ++ β) y β' z ->
    multistep α x (β ++ β') z.

Notation "α '⊧' t1 '↪*{' β '}' t2" := (multistep α t1 β t2) (at level 60, t1 constr, β constr).

Definition pure_multistep (t1 t2: tm) := forall α, α ⊧ t1 ↪*{ [] } t2.

Notation "t1 '↪*' t2" := (pure_multistep t1 t2) (at level 60, t1 constr, t2 constr).

Global Hint Constructors multistep : core.

Theorem multistep_trans :
  forall α βx βy (x y z : tm),
   α ⊧ x ↪*{ βx } y ->
   (α ++ βx) ⊧ y ↪*{ βy } z ->
   α ⊧ x ↪*{ βx ++ βy } z.
Proof.
  intros. generalize dependent z.
  induction H; intros.
  - simpl. rewrite <- app_nil_end in H0; eauto.
  - rewrite app_ass.
    apply multistep_step with y; auto. apply IHmultistep.
    rewrite app_ass; auto.
Qed.

Theorem multistep_R : forall α β (x y : tm),
    α ⊧ x ↪{ β } y -> α ⊧ x ↪*{ β } y.
Proof. intros.
  setoid_rewrite app_nil_end at 2. eauto.
Qed.

(* Definition normal_form (t : tm) : Prop := ~ exists t', t ↪ t'. *)

(* Definition deterministic {tm : Type} (R : relation tm) := *)
  (* forall x y1 y2 : tm, R x y1 -> R x y2 -> y1 = y2. *)

Lemma multi_step_regular: forall α β e1 e2, α ⊧ e1 ↪*{ β } e2 -> lc e1 /\ lc e2.
Admitted.

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

Lemma tlete_value_exists: forall α β e (v_x v: value),
    α ⊧ tlete v_x e ↪*{β} v <->
      lc v_x /\ body e /\ α ⊧ e ^t^ v_x ↪*{β} v.
Proof.
Admitted.

Lemma multi_step_value: forall α β (v: value) e,
    α ⊧ v ↪*{β} e ->
    e = treturn v.
Proof.
  intros * H.
  invclear H; eauto.
  easy.
Qed.
