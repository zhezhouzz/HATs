From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.
From CT Require Import RefinementType.
From CT Require Import RefinementTypeDenotation.
From CT Require Import RefinementTypeDenotationTac.
From CT Require Import RefinementTypeDenotationProp.
From CT Require Import InvDenotation.
From CT Require Import InvDenotationProp1.
From CT Require Import InvDenotationProp2.
From CT Require Import InvDenotationProp3.
From CT Require Import InvDenotationProp4.
From CT Require Import CtxDenotationProp.
From CT Require Import Typing.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import OperationalSemanticsProp.
Import BasicTyping.
Import SyntaxSugar.
Import TermOrdering.
Import RefinementType.
Import RefinementTypeTac.
Import RefinementTypeDenotation.
Import RefinementTypeDenotationTac.
Import RefinementTypeDenotationProp.
Import WFCtxDenotation.
Import WFCtxDenotationProp.
Import InvDenotation.
Import InvDenotationProp1.
Import InvDenotationProp2.
Import InvDenotationProp3.
Import InvDenotationProp4.
Import CtxDenotation.
Import CtxDenotationProp.
Import Typing.

(** We use the invariant denotation *)
Theorem soundness_aux: forall (Γ: listctx rty) (e: tm) (τ: rty), Γ ⊢ e ⋮t τ -> ⅋{∅}⟦ τ ⟧{ Γ } e.
Proof.
  apply (term_under_type_check_rec
           (fun Γ v τ _ => ⅋{∅}⟦ τ ⟧{ Γ } v)
           (fun Γ e τ _ => ⅋{∅}⟦ τ ⟧{ Γ } e)); intros Γ; intros; mydestr; try soundness_simp.
  (** constant *)
  - apply inv_rRctx_pre_weakening_empty; auto.
  (** var base *)
  - apply ctxfind_some_spec in H; auto; mydestr; subst.
    rewrite app_assoc.
    apply inv_rRctx_pre_weakening; refinement_solver.
    apply wf_ctxrR_implies_inv_var_over_last.
    eapply wf_ctxrR_weaken; listctx_set_simpl; eauto.
  - apply ctxfind_some_spec in H; auto; mydestr; subst.
    rewrite app_assoc.
    apply inv_rRctx_pre_weakening; refinement_solver.
    apply wf_ctxrR_implies_inv_var_under_last.
    eapply wf_ctxrR_weaken; listctx_set_simpl; eauto.
  (** var arr *)
  - apply ctxfind_some_spec in e; auto; mydestr; subst.
    rewrite app_assoc.
    apply inv_rRctx_pre_weakening; refinement_solver.
    apply wf_ctxrR_implies_inv_var_is_arr_last; auto.
    eapply wf_ctxrR_implies_inner_closed_rty; eauto.
    eapply wf_ctxrR_weaken; listctx_set_simpl; eauto.
  (** lam *)
  - auto_pose_fv x. repeat specialize_with x.
    eapply inv_rRctx_oarr; eauto; try closed_rty_solver; refinement_solver.
    apply rty_judgement_implies_wf in t; eauto. soundness_simp; auto.
  - auto_pose_fv x. repeat specialize_with x.
    eapply inv_rRctx_arrarr; eauto; try closed_rty_solver; refinement_solver.
    apply rty_judgement_implies_wf in t. soundness_simp; auto.
  (** fix *)
  - apply wf_ctxrR_implies_fix; auto. closed_rty_solver.
  (** value *)
  - auto.
  (** err *)
  - apply inv_rRctx_pre_weakening_empty; auto.
  (** sub *)
  - apply subtyping_spec with (e := e) in s; RD_simp2; auto.
    + RD_simp. apply inv_rRctx_pre_weakening_empty; auto.
  (** eq *)
  - apply subtyping_spec with (e := e) in s.
    apply subtyping_spec with (e := e) in s0.
    RD_simp2. RD_simp2. RD_simp2.
  (** merge *)
  - match goal with
    | [H: _ ⊢ _ ⩔ _ ⩵ _ |- _ ] => unfold disjunction in H; erewrite <- H; split; auto
    end.
  (** lete *)
  - auto_pose_fv x. repeat specialize_with x. eapply wf_implies_ctxrR_tlete_ubase_drop in H0; eauto. setoid_rewrite close_open_var_tm in H0; fast_set_solver.
    apply rty_judgement_implies_wf in t0. soundness_simp; auto.
    refinement_solver.
  - auto_pose_fv x. repeat specialize_with x. eapply wf_implies_ctxrR_tlete_is_arr_drop in H0; eauto. setoid_rewrite close_open_var_tm in H0; fast_set_solver.
    apply rty_judgement_implies_wf in t0. soundness_simp; auto.
    refinement_solver.
  (** letop *)
  - auto_pose_fv x. repeat specialize_with x.
    apply inv_implies_ctxrR_drop_last with (x:=x) (τ_x:= ({1 ~r> v2} (mk_op_ret op ^r^ v1))); eauto; try fast_set_solver.
    + apply rty_judgement_implies_wf in t. soundness_simp; auto.
    + refinement_solver.
    + eapply inv_rRctx_tletbiop; eauto; try fast_set_solver.
      apply rty_judgement_implies_wf in t. soundness_simp; auto.
  (** letapp *)
  - auto_pose_fv x. repeat specialize_with x.
    apply rty_judgement_implies_wf in t. soundness_simp; auto.
    assert (is_arr τ2 /\ not_overbasety τ_x) as (Hno1 & Hno2).
    { apply inv_ctxrR_regular in H; mydestr.
      rewrite closed_rty_destruct_arrarr in H11; mydestr; auto. }
    assert ((⅋{∅}⟦τ⟧{Γ ++ [(x, τ_x)] }) (tletapp v1 v2 e)).
    eapply inv_rRctx_letapp_arrarr; eauto. fast_set_solver.
    refinement_solver.
    eapply inv_implies_ctxrR_drop_last in H6; eauto; try fast_set_solver.
    refinement_solver.
  - assert (∃ L : aset, ∀ x : atom, x ∉ L → wf_ctxrR ∅ (Γ ++ [(x, [v:b|0|d|ϕ])])).
    { apply rty_judgement_implies_wf_value in v.
      apply wf_typing_implies_last_wf_ctxrR in v; auto. }
    destruct H5 as (Lwf & Hwf).
    auto_pose_fv x. repeat specialize_with x.
    apply rty_judgement_implies_wf in t. soundness_simp; auto.
    assert (not_overbasety τ_x) as Hno.
    { apply inv_ctxrR_regular in H; mydestr.
      rewrite closed_rty_destruct_oarr in H11; mydestr; auto. }
    assert ((⅋{∅}⟦τ⟧{Γ ++ [(x, τ_x ^r^ v2)] }) (tletapp v1 v2 e)).
    eapply inv_rRctx_letapp_oarr; eauto. fast_set_solver.
    refinement_solver.
    eapply inv_implies_ctxrR_drop_last in H6; eauto; try fast_set_solver.
    refinement_solver.
  (** matchb *)
  - eapply inv_rRctx_matchb_true; eauto. refinement_solver.
  - eapply inv_rRctx_matchb_false; eauto. refinement_solver.
Qed.

(** Soundness (also the fundamental theorem of the logical relation) *)
Theorem soundness: forall (Γ: listctx rty) (e: tm) (τ: rty), Γ ⊢ e ⋮t τ -> {∅}⟦ τ ⟧{ Γ } e.
Proof.
  intros.
  assert (not_overbasety τ). apply rty_judgement_implies_wf in H; soundness_simp; auto.
  apply soundness_aux in H.
  eapply inv_ctxrR_implies_ctxrR; eauto.
Qed.
