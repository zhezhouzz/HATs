From stdpp Require Import mapset.
From stdpp Require Import natmap.
From stdpp Require Import fin_map_dom.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.
From CT Require Import RefinementType.
From CT Require Import RefinementTypeTac.
From CT Require Import RefinementTypeDenotation.
From CT Require Import RefinementTypeDenotationTac.
From CT Require Import RefinementTypeDenotationProp.
From CT Require Import InvDenotation.
From CT Require Import InvDenotationProp1.
From CT Require Import InvDenotationProp2.
From CT Require Import TermOrdering.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.

Import Atom.
Import CoreLang.
Import CoreLangProp.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import OperationalSemanticsProp.
Import BasicTyping.
Import SyntaxSugar.
Import RefinementType.
Import RefinementTypeTac.
Import RefinementTypeDenotation.
Import RefinementTypeDenotationTac.
Import RefinementTypeDenotationProp.
Import WFCtxDenotation.
Import WFCtxDenotationProp.
Import NamelessTactics.
Import TermOrdering.
Import InvDenotation.
Import InvDenotationProp1.
Import InvDenotationProp2.

Global Hint Resolve mk_eq_constant_is_not_overbasety: core.
Global Hint Resolve mk_eq_var_is_not_overbasety: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Constructors ok_dctx: core.
Global Hint Resolve rR_implies_no_free: core.
Global Hint Resolve ctxrR_tlete_drop_halt_lhs: core.
Global Hint Resolve rR_implies_reduction_no_free: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Resolve under_not_overbasety: core.
Global Hint Resolve is_arr_open_trans: core.


Lemma wf_implies_ctxrR_tlete_ubase_better_drop
     : ∀ (Γ : list (atom * rty)) (st : state) (x : atom) (b : base_ty)
         (n : nat) (d : aset) (ϕ : refinement) (e_x e : tm) (τ : rty),
    x ∉ stale e ∪ stale τ -> closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) τ ->
         wf_ctxrR st (Γ ++ [(x, [v:b|n|d|ϕ])])
         → not_overbasety τ
           → (⅋{st}⟦[v:b|n|d|ϕ]⟧{Γ}) e_x
             → (⅋{st}⟦τ⟧{Γ ++ [(x, [v:b|n|d|ϕ])] }) (e ^t^ x)
               → (⅋{st}⟦τ⟧{Γ}) (tlete e_x e).
Proof.
  intros. rewrite <- (close_open_var_tm e x 0); try fast_set_solver.
  assert ((⅋{st}⟦τ⟧{Γ ++ [(x, [v:b|n|d|ϕ])] }) (tlete e_x (x \t\ (e ^t^ x)))).
  eapply wf_implies_ctxrR_tlete_ubase; eauto.
  eapply inv_implies_ctxrR_drop_last; eauto.
  - fast_set_solver.
  - assert (x ∉ fv_tm e_x). inv_rd_solver1.
    assert (x ∉ fv_tm (x \t\ (e ^t^ x))) by apply close_rm_fv_tm.
    set_solver.
Qed.

Lemma wf_implies_ctxrR_tlete_ubase_better
     : ∀ (Γ : list (atom * rty)) (st : state) (x : atom) (b : base_ty)
         (n : nat) (d : aset) (ϕ : refinement) (e_x e : tm) (τ : rty),
    x ∉ stale e ->
         wf_ctxrR st (Γ ++ [(x, [v:b|n|d|ϕ])])
         → not_overbasety τ
           → (⅋{st}⟦[v:b|n|d|ϕ]⟧{Γ}) e_x
             → (⅋{st}⟦τ⟧{Γ ++ [(x, [v:b|n|d|ϕ])] }) (e ^t^ x)
               → (⅋{st}⟦τ⟧{Γ ++ [(x, [v:b|n|d|ϕ])] }) (tlete e_x e).
Proof.
  intros. rewrite <- (close_open_var_tm e x 0); try fast_set_solver.
  eapply wf_implies_ctxrR_tlete_ubase; eauto.
Qed.

Lemma wf_implies_ctxrR_tlete_is_arr_better:
  ∀ (Γ : list (atom * rty)) (st : state) (x : atom) (τ_x : rty)
    (e_x : value) (e : tm) (τ : rty),
    x ∉ stale e ->
    wf_ctxrR st (Γ ++ [(x, τ_x)])
    → not_overbasety τ
      → is_arr τ_x
        → (⅋{st}⟦τ_x⟧{Γ}) e_x
          → (⅋{st}⟦τ⟧{Γ ++ [(x, τ_x)] }) (e ^t^ x)
          → (⅋{st}⟦τ⟧{Γ ++ [(x, τ_x)] }) (tlete e_x e).
Proof.
  intros. rewrite <- (close_open_var_tm e x 0); try fast_set_solver.
  eapply wf_implies_ctxrR_tlete_is_arr; eauto.
Qed.

Lemma wf_implies_ctxrR_tlete_ubase_better_empty
  : ∀ (st : state) (x : atom) (b : base_ty)
      (n : nat) (d : aset) (ϕ : refinement) (e_x e : tm) (τ : rty),
    x ∉ stale e -> wf_ctxrR st ([(x, [v:b|n|d|ϕ])])
    → not_overbasety τ
    → ({0;b∅;st}⟦[v:b|n|d|ϕ]⟧ e_x)
    → (⅋{st}⟦τ⟧{ [(x, [v:b|n|d|ϕ])] }) (e ^t^ x)
    → (⅋{st}⟦τ⟧{ [(x, [v:b|n|d|ϕ])] }) (tlete e_x e).
Proof.
  intros. assert ((⅋{st}⟦τ⟧{ [] ++ [(x, [v:b|n|d|ϕ])] }) (tlete e_x e)).
  apply wf_implies_ctxrR_tlete_ubase_better; RD_simp2; auto. listctx_set_simpl.
Qed.

Lemma wf_implies_ctxrR_tlete_is_arr_better_empty:
  ∀ (st : state) (x : atom) (τ_x : rty)
    (e_x : value) (e : tm) (τ : rty),
    x ∉ stale e ->
    wf_ctxrR st ([(x, τ_x)])
    → not_overbasety τ
      → is_arr τ_x
        → ({0;b∅;st}⟦τ_x⟧ e_x)
          → (⅋{st}⟦τ⟧{[(x, τ_x)] }) (e ^t^ x)
          → (⅋{st}⟦τ⟧{[(x, τ_x)] }) (tlete e_x e).
Proof.
  intros. assert ((⅋{st}⟦τ⟧{ [] ++ [(x, τ_x)] }) (tlete e_x e)).
  apply wf_implies_ctxrR_tlete_is_arr_better; RD_simp2; auto. listctx_set_simpl.
Qed.

Lemma termR_perserve_inv_ctxrR: forall Γ τ (e e': tm),
    not_overbasety τ ->
    valid_rty τ ->
    e <-<{ ⌊ Γ ⌋* ;  ⌊ τ ⌋ } e' -> (forall st, ⅋{st}⟦τ⟧{Γ} e -> ⅋{st}⟦τ⟧{Γ} e').
Proof.
  induction Γ; intros; invclear H2.
  - constructor. intros. eapply termR_perserve_rR; eauto.
  - constructor; auto. termR_solver.
    intros. apply IHΓ with (e:= ({x := c_x }t e)); eauto. denotation_simp.
    apply termR_tm_subst with (Tx := B); eauto. refinement_solver. denotation_simp3.
    termR_solver.
  - constructor; auto. termR_solver.
    destruct H11 as (e_x_hat & He_x_hat & HH). exists e_x_hat. split; auto.
    intros. auto_under v_x. eapply IHΓ; eauto.
    eapply termR_tm_subst with (Tx := b); eauto. denotation_simp. refinement_solver.
    simpl in H1. termR_solver.
  - constructor; auto. termR_solver. termR_solver. auto_under v_x.
    eapply IHΓ; eauto.
    eapply termR_tm_subst with (Tx := ⌊τ_x⌋); eauto. denotation_simp. refinement_solver.
    simpl in H1. termR_solver.
Qed.

Lemma letapp_aux_typable: forall st τ x τ_x e y,
    x <> y -> x ∉ stale e ->
    (⅋{st}⟦τ⟧{ [(x, τ_x)] } (e ^t^ x)) -> ([(x, ⌊ τ_x ⌋)] ++ [(y, ⌊ τ_x ⌋)]) ⊢t e ^t^ y ⋮t ⌊τ⌋.
Proof.
  intros.
  apply inv_ctxrR_regular in H1; mydestr. simpl in H1.
  assert (([] ++ [(x, ⌊τ_x⌋)]) ⊢t (e ^t^ x) ⋮t ⌊τ⌋); auto; try listctx_set_solver.
  apply basic_has_type_renaming with (x0:=y) in H5; try listctx_set_solver.
  lc_simpl4. simpl in H5.
  apply basic_typing_weaken_tm_post; auto; listctx_set_solver.
Qed.

Lemma rR_letapp_base': forall τ_x τ st x (v1 v2: value) (e: tm) b n d ϕ,
    x ∉ fv_tm e ∪ rty_fv τ ->
    not_overbasety τ -> not_overbasety τ_x ->
    (∀ e_wf : tm, ({0;b∅;st}⟦[v:b|n|d|ϕ]⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) ->
    wf_ctxrR st [(x, τ_x ^r^ v2)] ->
    {0;b∅;st}⟦-:{v: b | n | d | ϕ}⤑ τ_x⟧ v1 ->
    {0;b∅;st}⟦[v:b|n|d|ϕ]⟧ v2 ->
    (⅋{st}⟦τ⟧{[(x, τ_x ^r^ v2)] }) (e ^t^ x) ->
    (* {0;b∅;st}⟦τ⟧ (tletapp v1 v2 e). *)
    (⅋{st}⟦τ⟧{[(x, τ_x ^r^ v2)] }) (tletapp v1 v2 e).
Proof.
  intros.
  assert (exists c2: constant, v2 = c2 /\ ϕ b∅ st c2 /\ [] ⊢t c2 ⋮v b); mydestr; subst.
  { eapply wf_implies_base_phi_sat_v in H2; eauto. }
  destruct (decide (is_arr τ_x)); intros.
  - destruct (rR_arrow_value_lam_exists_oarr _ _ _ _ _ _ _ _ _ H4); mydestr; subst.
    + rename x1 into e1.
      assert (({0;b∅;st}⟦τ_x ^r^ x0⟧) (e1 ^t^ x0)) as Hz.
      { eapply rR_letapp_overbase_lam in H4; eauto. }
      assert (is_arr (τ_x ^r^ x0)) as Hzz; auto.
      pose (rR_arr_halt _ _ _ _ _ Hzz Hz). mydestr.
      apply wf_implies_ctxrR_tlete_is_arr_better_empty with (x:=x) (e:=e) (τ:=τ) in H7; eauto; try fast_set_solver.
      eapply termR_perserve_inv_ctxrR; eauto.
      { invclear H7; refinement_solver. }
      apply termR_trans_better with (tlete (e1 ^t^ x0) e).
      simpl. apply termR_weakening. listctx_set_solver.
      eapply termR_elete_lhs with (x:=x); eauto; try inv_rd_simpl1.
      apply termR_value_tm; auto; refinement_solver.
      simpl. apply termR_tletapp_lam with (Ty := ⌊ τ_x ⌋); auto; inv_rd_simpl1.
      basic_typing_solver. refinement_solver. basic_typing_solver.
      auto_exists_L. intros.
      eapply letapp_aux_typable in H6; eauto; inv_rd_simpl1.
    + rename x1 into e1.
      assert (({0;b∅;st}⟦τ_x ^r^ x0⟧) (({1 ~t> x0} e1) ^t^ (vfix (b ⤍ ⌊τ_x⌋) (vlam b e1)))) as Hz.
      { eapply rR_letapp_overbase_fix in H4; eauto. }
      assert (is_arr (τ_x ^r^ x0)) as Hzz; auto.
      pose (rR_arr_halt _ _ _ _ _ Hzz Hz). mydestr.
      apply wf_implies_ctxrR_tlete_is_arr_better_empty with (x:=x) (e:=e) (τ:=τ) in H7; eauto; try fast_set_solver.
      eapply termR_perserve_inv_ctxrR; eauto.
      { invclear H7; refinement_solver. }
      apply termR_trans_better with (tlete (({1 ~t> x0} e1) ^t^ (vfix (b ⤍ ⌊τ_x⌋) (vlam b e1))) e).
      apply termR_weakening. listctx_set_solver.
      eapply termR_elete_lhs with (x:=x); eauto; try inv_rd_simpl1.
      apply termR_value_tm; auto; refinement_solver.
      simpl. apply termR_tletapp_fix; auto.
      basic_typing_solver. refinement_solver. basic_typing_solver.
      auto_exists_L. intros.
      eapply letapp_aux_typable in H6; eauto; inv_rd_simpl1.
  - destruct τ_x; try auto_ty_exfalso. invclear H1.
    destruct (rR_arrow_value_lam_exists_oarr _ _ _ _ _ _ _ _ _ H4); mydestr; subst.
    + rename x5 into e1.
      assert (({0;b∅;st}⟦[v:x1|x2|x3|x4] ^r^ x0⟧) (e1 ^t^ x0)) as Hz.
      { eapply rR_letapp_overbase_lam in H4; eauto. }
      apply wf_implies_ctxrR_tlete_ubase_better_empty with (x:=x) (e:=e) (τ:=τ) in Hz; eauto; try fast_set_solver.
      eapply termR_perserve_inv_ctxrR; eauto.
      { invclear Hz; refinement_solver. }
      simpl. apply termR_tletapp_lam with (Ty := x1); eauto.
      basic_typing_solver. refinement_solver. basic_typing_solver.
      auto_exists_L. intros.
      eapply letapp_aux_typable in H6; eauto; fast_set_solver.
    + rename x5 into e1.
      assert (({0;b∅;st}⟦[v:x1|x2|x3|x4] ^r^ x0⟧) (({1 ~t> x0} e1) ^t^ (vfix (b ⤍ x1) (vlam b e1)))) as Hz.
      { eapply rR_letapp_overbase_fix in H4; eauto. }
      apply wf_implies_ctxrR_tlete_ubase_better_empty with (x:=x) (e:=e) (τ:=τ) in Hz; eauto; try fast_set_solver.
      eapply termR_perserve_inv_ctxrR; eauto.
      { invclear Hz; refinement_solver. }
      simpl. apply termR_tletapp_fix; auto.
      basic_typing_solver. refinement_solver. basic_typing_solver.
      auto_exists_L. intros.
      eapply letapp_aux_typable in H6; eauto; fast_set_solver.
Qed.
