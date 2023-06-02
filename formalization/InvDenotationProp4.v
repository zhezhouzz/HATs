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
From CT Require Import InvDenotationProp3.
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
Import InvDenotationProp3.

Global Hint Resolve mk_eq_constant_is_not_overbasety: core.
Global Hint Resolve mk_eq_var_is_not_overbasety: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Constructors ok_dctx: core.
Global Hint Resolve rR_implies_no_free: core.
Global Hint Resolve ctxrR_tlete_drop_halt_lhs: core.
Global Hint Resolve rR_implies_reduction_no_free: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Resolve under_not_overbasety: core.

Lemma fix_rR_aux_c: forall st b n d ϕ τ e,
    [] ⊢t vfix (TBase b ⤍ ⌊τ⌋) (vlam b e) ⋮v (TBase b ⤍ ⌊τ⌋) ->
    closed_rty 0 (dom aset st) (-:{v: b | n | d | ϕ}⤑ τ) ->
    forall (c: constant),
    {0;b∅;st}⟦{v: b | n | d | ϕ}⟧ c ->
    (forall (c_x: constant),
        {0;b∅;st}⟦{v: b | n | d | ϕ}⟧ c_x ->
        ({1;<b[↦c_x]> b∅;st}⟦(-:{v: b | S n | d | ≻≻ ϕ}⤑ τ) ⤑ τ⟧) ((vlam (b ⤍ ⌊τ⌋) e) ^t^ c_x)) ->
    ({1;<b[↦c]> b∅;st}⟦τ⟧) (({1 ~t> c} e) ^t^ (vfix (b ⤍ ⌊τ⌋) (vlam b e))).
Proof.
  intros st b n d ϕ τ e HTfix Hclosed.
  apply (well_founded_induction_type well_founded_R_constant_is_well_founded
           (fun c =>
                {0;b∅;st}⟦{v: b | n | d | ϕ}⟧ c ->
                (forall (c_x: constant),
                    {0;b∅;st}⟦{v: b | n | d | ϕ}⟧ c_x ->
                    ({1;<b[↦c_x]> b∅;st}⟦(-:{v: b | S n | d | ≻≻ ϕ}⤑ τ) ⤑ τ⟧) ((vlam (b ⤍ ⌊τ⌋) e) ^t^ c_x)) ->
                ({1;<b[↦c]> b∅;st}⟦τ⟧) (({1 ~t> c} e) ^t^ (vfix (b ⤍ ⌊τ⌋) (vlam b e))))
        ).
  intros c; intros.
  assert (({1;<b[↦c]> b∅;st}⟦(-:{v: b | S n | d | ≻≻ ϕ}⤑ τ) ⤑ τ⟧)
             (vlam (b ⤍ ⌊τ⌋) e ^t^ c)) as Hz; auto.
  destruct Hz. destruct H3. do 2 destruct H4. simpl in H4.
  assert (x = (vlam (b ⤍ ⌊τ⌋) ({1 ~t> c }e))) by (reduction_simpl1; auto); subst. clear H4.
  assert (({1;<b[↦c]> b∅;st}⟦-:{v: b | S n | d | ≻≻ ϕ}⤑ τ⟧) (vfix (b ⤍ ⌊τ⌋) (vlam b e))).
  - constructor; auto. constructor; auto. auto_dclosed_rty.
    exists (vfix (b ⤍ ⌊τ⌋) (vlam b e)). split; eauto. apply multistep_refl. basic_typing_solver.
    intros c'. intros.
    assert (c ≻ c').
    { eapply well_founded_phi_implies_lt; eauto.
      simpl in H0; mydestr; subst. invclear H10. auto. }
    assert (({1;<b[↦c']> b∅;st}⟦τ⟧) (mk_app (vfix (b ⤍ ⌊τ⌋) (vlam b e)) c')).
    eapply termR_perserve_rR; auto. refinement_solver. refinement_solver.
    apply mk_app_reduce_to_open_fix'; auto.
    eapply H; eauto.
    + constructor; auto. constructor; auto. auto_dclosed_rty.
      exists c'. split; auto. split; auto. apply well_founded_phi_implies_phi in H6.
      auto_dclosed_rty. rewrite closed_obase_implies_all_bst in H6; eauto.
    + rewrite rR_bst_bound in H8; eauto.
      rewrite rR_implies_bound_plus1 in H8; mydestr; eauto.
      unfold bst_eq. unfold bstate_push. intros.
      destruct i; auto. destruct i; auto. lia.
  - auto_under (vfix (b ⤍ ⌊τ⌋) (vlam b e)).
    apply termR_perserve_rR with (e':=({1 ~t> c} e) ^t^ (vfix (b ⤍ ⌊τ⌋) (vlam b e))) in H5; auto.
    refinement_solver. refinement_solver.
    apply mk_app_reduce_to_open; auto.
    eapply vfix_implies_open_tyable with (v2:=c) in HTfix; eauto.
    refinement_solver.
Qed.

Lemma fix_rR: forall τ st b n d ϕ e,
    closed_rty 0 (dom aset st) (-:{v: b | n | d | ϕ}⤑ τ) ->
    {0;b∅;st}⟦-:{v: b | n | d | ϕ}⤑ (-:{v: b | S n | d | ≻≻ ϕ}⤑ τ) ⤑ τ⟧ (vlam b (vlam (b ⤍ ⌊τ⌋) e)) ->
    {0;b∅;st}⟦-:{v: b | n | d | ϕ}⤑ τ⟧ (vfix (b ⤍ ⌊τ⌋) (vlam b e)).
Proof.
  intros. destruct H0. destruct H1. do 2 destruct H2.
  assert ([] ⊢t vfix (b ⤍ ⌊τ⌋) (vlam b e) ⋮t b ⤍ ⌊τ⌋) as HT.
  { basic_typing_solver. invclear H6.
    auto_exists_L. intros; eauto.
    assert (f ∉ L) by fast_set_solver. apply H5 in H4. invclear H4; auto. }
  assert (x = vlam b (vlam (b ⤍ ⌊τ⌋) e)) by (reduction_simpl1; auto); subst. clear H2.
  do 2 (constructor; auto).
  exists (vfix (b ⤍ ⌊τ⌋) (vlam b e)). split; eauto. apply multistep_refl. basic_typing_solver.
  intros. auto_dclosed_rty.
  eapply termR_perserve_rR; auto. refinement_solver.
  apply mk_app_reduce_to_open_fix'; auto. basic_typing_solver.
  apply fix_rR_aux_c with (n:=n) (d:=d) (ϕ:=ϕ); eauto.
  - basic_typing_solver.
  - auto_dclosed_rty.
  - do 2 (constructor; eauto).
  - intros. simpl in H14; mydestr; subst. invclear H18.
    apply H3 in H17; auto.
    eapply termR_perserve_rR; eauto.
    { invclear H12. constructor; auto. constructor; auto. invclear H5. invclear H12. auto. }
    apply mk_app_reduce_to_open; auto. inv_rd_simpl1.
Qed.

Lemma wf_ctxrR_implies_fix: forall Γ st b d ϕ τ e,
  wf_ctxrR st Γ ->
  closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) (-:{v: b | 0 | d | ϕ}⤑ τ) ->
  (⅋{st}⟦-:{v: b | 0 | d | ϕ}⤑ (-:{v: b | 1 | d | ≻≻ ϕ}⤑ τ) ⤑ τ⟧{Γ}) (vlam b (vlam (b ⤍ ⌊τ⌋) e)) ->
  (⅋{st}⟦-:{v: b | 0 | d | ϕ}⤑ τ⟧{Γ}) (vfix (b ⤍ ⌊τ⌋) (vlam b e)).
Proof.
  induction Γ; intros. RD_simp2. apply fix_rR; auto. closed_rty_solver.
  mydestr.
  assert (((a, ⌊r⌋) :: ⌊Γ⌋*) ⊢t vfix (b ⤍ ⌊τ⌋) (vlam b e) ⋮t ⌊-:{v: b | 0 | d | ϕ}⤑ τ⌋) as HT.
          { apply inv_ctxrR_regular in H1; mydestr.
            basic_typing_solver. invclear H7.
            auto_exists_L. intros; eauto.
            assert (f ∉ L) by fast_set_solver. apply H6 in H5. invclear H5; auto.
          }
          RD_simp2.
  - constructor; auto.
    intros. auto_under c_x. simpl.
    apply IHΓ; auto. closed_rty_solver.
  - constructor; auto.
    mydestr. auto_meet_exists Hmeet. auto_meet_reduce.
    simpl. apply IHΓ; eauto; dsimp1. refinement_solver. split; auto. refinement_solver.
  - constructor; auto. inv_rd_simpl1.
    intros. auto_under v_x. simpl.
    apply IHΓ; auto. inv_rd_simpl1.
Qed.

Lemma rR_letapp_arr: forall τ_x τ st x (v1 v2: value) (e: tm) τ2,
    x ∉ fv_tm e ∪ rty_fv τ ->
    not_overbasety τ -> not_overbasety τ_x -> is_arr τ2 ->
    wf_ctxrR st [(x, τ_x)] ->
    {0;b∅;st}⟦τ2 ⤑ τ_x⟧ v1 ->
    {0;b∅;st}⟦τ2⟧ v2 ->
    (⅋{st}⟦τ⟧{[(x, τ_x)] }) (e ^t^ x) ->
    (⅋{st}⟦τ⟧{[(x, τ_x)] }) (tletapp v1 v2 e).
Proof.
  intros.
  destruct (decide (is_arr τ_x)); intros.
  - destruct (rR_arrow_value_lam_exists_arrarr _ _ _ _ _ _ H4); mydestr; subst.
    + rename x0 into e1.
      assert (({0;b∅;st}⟦τ_x⟧) (e1 ^t^ v2)) as Hz.
      { eapply rR_letapp_arr_lam in H4; eauto. }
      pose (rR_arr_halt _ _ _ _ _ i Hz). mydestr.
      apply wf_implies_ctxrR_tlete_is_arr_better_empty with (x:=x) (e:=e) (τ:=τ) in H7; eauto; try fast_set_solver.
      eapply termR_perserve_inv_ctxrR; eauto.
      { invclear H7; refinement_solver. }
      apply termR_trans_better with (tlete (e1 ^t^ v2) e).
      simpl. apply termR_weakening. listctx_set_solver.
      eapply termR_elete_lhs with (x:=x); eauto; try inv_rd_simpl1.
      apply termR_value_tm; auto; refinement_solver.
      eapply termR_weakening. listctx_set_solver.
      simpl. apply termR_tletapp_lam with (Ty := ⌊ τ_x ⌋); auto; inv_rd_simpl1.
      refinement_solver. refinement_solver.
      auto_exists_L. intros. inv_rd_simpl1. simpl in H6.
      assert ( ([] ++ [(x, ⌊τ_x⌋)]) ⊢t e ^t^ x ⋮t ⌊τ⌋) as Hr by auto.
      apply basic_has_type_renaming with (x0:=y) in Hr. lc_simpl4. fast_set_solver.
      listctx_set_solver.
    + rename x0 into e1.
      assert (({0;b∅;st}⟦τ_x⟧) (({1 ~t> v2} e1) ^t^ (vfix (⌊ τ2 ⌋ ⤍ ⌊τ_x⌋) (vlam ⌊ τ2 ⌋ e1)))) as Hz.
      { eapply rR_letapp_arr_fix in H4; eauto. }
      pose (rR_arr_halt _ _ _ _ _ i Hz). mydestr.
      apply wf_implies_ctxrR_tlete_is_arr_better_empty with (x:=x) (e:=e) (τ:=τ) in H7; eauto; try fast_set_solver.
      eapply termR_perserve_inv_ctxrR; eauto.
      { invclear H7; refinement_solver. }
      apply termR_trans_better with (tlete (({1 ~t> v2} e1) ^t^ (vfix (⌊ τ2 ⌋ ⤍ ⌊τ_x⌋) (vlam ⌊ τ2 ⌋ e1))) e).
      simpl. apply termR_weakening. listctx_set_solver.
      eapply termR_elete_lhs with (x:=x); eauto; try inv_rd_simpl1.
      apply termR_value_tm; auto; refinement_solver.
      eapply termR_weakening. listctx_set_solver.
      simpl. apply termR_tletapp_fix; auto; inv_rd_simpl1.
      refinement_solver. refinement_solver.
      auto_exists_L. intros. inv_rd_simpl1. simpl in H6.
      assert ( ([] ++ [(x, ⌊τ_x⌋)]) ⊢t e ^t^ x ⋮t ⌊τ⌋) as Hr by auto.
      apply basic_has_type_renaming with (x0:=y) in Hr. lc_simpl4. fast_set_solver.
      listctx_set_solver.
  - auto_ty_exfalso.
    destruct (rR_arrow_value_lam_exists_arrarr _ _ _ _ _ _ H4); mydestr; subst.
    + rename x4 into e1.
      assert (({0;b∅;st}⟦[v:x0|x1|x2|x3]⟧) (e1 ^t^ v2)) as Hz.
      { eapply rR_letapp_arr_lam in H4; eauto. }
      apply wf_implies_ctxrR_tlete_ubase_better_empty with (x:=x) (e:=e) (τ:=τ) in Hz; eauto; try fast_set_solver.
      eapply termR_perserve_inv_ctxrR; eauto.
      { invclear Hz; refinement_solver. }
      apply termR_weakening. listctx_set_solver.
      apply termR_tletapp_lam with (Ty := x0); eauto.
      refinement_solver. refinement_solver.
      auto_exists_L. intros. inv_rd_simpl1. simpl in H6.
      assert ( ([] ++ [(x, TBase x0)]) ⊢t e ^t^ x ⋮t ⌊τ⌋) as Hr by auto.
      apply basic_has_type_renaming with (x0:=y) in Hr. lc_simpl4. fast_set_solver.
      listctx_set_solver.
    + rename x4 into e1.
      assert (({0;b∅;st}⟦[v:x0|x1|x2|x3]⟧) (({1 ~t> v2} e1) ^t^ (vfix (⌊ τ2 ⌋ ⤍ x0) (vlam ⌊ τ2 ⌋ e1)))) as Hz.
      { eapply rR_letapp_arr_fix in H4; eauto. }
      apply wf_implies_ctxrR_tlete_ubase_better_empty with (x:=x) (e:=e) (τ:=τ) in Hz; eauto; try fast_set_solver.
      eapply termR_perserve_inv_ctxrR; eauto.
      { invclear Hz; refinement_solver. }
      apply termR_weakening. listctx_set_solver.
      apply termR_tletapp_fix; eauto.
      refinement_solver. refinement_solver.
      auto_exists_L. intros. inv_rd_simpl1. simpl in H6.
      assert ( ([] ++ [(x, TBase x0)]) ⊢t e ^t^ x ⋮t ⌊τ⌋) as Hr by auto.
      apply basic_has_type_renaming with (x0:=y) in Hr. lc_simpl4. fast_set_solver.
      listctx_set_solver.
Qed.

Global Hint Resolve rR_implies_no_free_value_unfold: core.

Global Hint Resolve rR_implies_no_free_value: core.

Lemma inv_rRctx_letapp_arrarr: forall Γ st (τ: rty) x τ2 τ_x (v1 v2: value) e,
    x ∉ fv_tm e ∪ rty_fv τ -> not_overbasety τ -> not_overbasety τ_x -> is_arr τ2 ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) τ ->
    wf_ctxrR st (Γ ++ [(x, τ_x)]) ->
    (⅋{st}⟦τ2 ⤑ τ_x⟧{Γ}) v1 ->
    (⅋{st}⟦τ2⟧{Γ}) v2 ->
    (⅋{st}⟦τ⟧{Γ ++ [(x, τ_x)] }) (e ^t^ x) ->
    ⅋{st}⟦τ⟧{Γ ++ [(x, τ_x)] } (tletapp v1 v2 e).
Proof.
  induction Γ; intros. listctx_set_simpl. invclear H5. invclear H6. eapply rR_letapp_arr; eauto.
  mydestr. assert (a ∉ dom aset st ∪ ctxdom Γ ∪ {[x]}) as Ha.
  { inv_rd_simpl0. apply wf_ctxrR_regular1 in H4; mydestr. refinement_solver. }
  assert (((a, ⌊ r ⌋) :: ⌊Γ ++ [(x, τ_x)]⌋*) ⊢t tletapp v1 v2 e ⋮t ⌊τ⌋) as HT.
          { denotation_simp.
            apply cons_basic_typing_drop_last_tm.
            apply inv_ctxrR_regular in H7; mydestr. apply ok_dctx_regular in H8; mydestr.
            inv_rd_simpl0.
            inv_rd_simpl1. inv_rd_simpl3.
            eapply tletapp_typable with (x:=x); eauto.
            fast_set_solver. inv_rd_simpl1. }
  RD_simp2; constructor; auto.
    - intros. auto_under c_x.
      eapply IHΓ; eauto; fold value_subst; fold tm_subst.
      + pose (fv_of_subst_tm a c_x e). set_solver.
      + refinement_solver.
      + rewrite <- subst_open_var_tm; auto. fast_set_solver.
   - mydestr. auto_meet_exists HE.
     auto_meet_reduce. dsimp1. rename x4 into c_x. auto_under x0.
     eapply IHΓ; eauto; fold value_subst; fold tm_subst.
      + pose (fv_of_subst_tm a c_x e). set_solver.
      + refinement_solver.
      + rewrite <- subst_open_var_tm; auto; fast_set_solver.
   - intros. auto_under v_x.
     apply IHΓ with (τ2 := τ2); eauto; fold value_subst; fold tm_subst.
     + pose (fv_of_subst_tm a v_x e).
       assert (fv_value v_x ≡ ∅) by eauto.
       rewrite H6 in s. set_solver.
      + simpl in H3. dec_solver2.
      + rewrite <- subst_open_var_tm; auto. fast_set_solver. refinement_solver.
Qed.

Lemma inv_rRctx_matchb_true: forall Γ st (τ: rty) (v: value) e1 e2,
    not_overbasety τ ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) τ ->
    wf_ctxrR st Γ ->
    (⅋{st}⟦mk_eq_constant true⟧{Γ}) v ->
    (⅋{st}⟦τ⟧{Γ}) e1 ->
    ⌊ Γ ⌋* ⊢t e2 ⋮t ⌊ τ ⌋ ->
    (⅋{st}⟦τ⟧{Γ}) (tmatchb v e1 e2).
Proof.
  induction Γ; intros.
  { RD_simp2. apply rR_mk_eq_constant_bool in H3; subst. eapply termR_perserve_rR; eauto.
    refinement_solver. apply termR_tmatchb_true; auto. refinement_solver. }
  mydestr.
  assert (a ∉ dom aset st ∪ ctxdom Γ) as Ha. {
    inv_rd_simpl0. apply wf_ctxrR_regular1 in H1; mydestr. refinement_solver. }
  assert (((a, ⌊ r ⌋) :: ⌊Γ⌋*) ⊢t (tmatchb v e1 e2) ⋮t ⌊τ⌋) as HT by inv_rd_simpl1.
  RD_simp2; constructor; auto.
 - intros. auto_under c_x.
            eapply IHΓ; eauto; fold value_subst; fold tm_subst.
            + refinement_solver.
            + eapply basic_typing_subst_tm_post in H4; eauto.
              refinement_solver.
          - mydestr. auto_meet_exists HE.
            auto_meet_reduce. dsimp1. rename x2 into c_x. auto_under x0.
            eapply IHΓ; eauto; fold value_subst; fold tm_subst.
            + refinement_solver.
            + eapply basic_typing_subst_tm_post; eauto.
          - intros. auto_under v_x.
            apply IHΓ; eauto; fold value_subst; fold tm_subst.
            eapply basic_typing_subst_tm_post in H4; eauto. refinement_solver.
Qed.

Lemma inv_rRctx_matchb_false: forall Γ st (τ: rty) (v: value) e1 e2,
    not_overbasety τ ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) τ ->
    wf_ctxrR st Γ ->
    (⅋{st}⟦mk_eq_constant false⟧{Γ}) v ->
    (⅋{st}⟦τ⟧{Γ}) e2 ->
    ⌊ Γ ⌋* ⊢t e1 ⋮t ⌊ τ ⌋ ->
    (⅋{st}⟦τ⟧{Γ}) (tmatchb v e1 e2).
Proof.
  induction Γ; intros.
  { RD_simp2. apply rR_mk_eq_constant_bool in H3; subst. eapply termR_perserve_rR; eauto.
    refinement_solver. apply termR_tmatchb_false; auto. refinement_solver. }
  mydestr.
  assert (a ∉ dom aset st ∪ ctxdom Γ) as Ha. {
    inv_rd_simpl0. apply wf_ctxrR_regular1 in H1; mydestr. refinement_solver. }
  assert (((a, ⌊ r ⌋) :: ⌊Γ⌋*) ⊢t (tmatchb v e1 e2) ⋮t ⌊τ⌋) as HT by inv_rd_simpl1.
  RD_simp2; constructor; auto.
 - intros. auto_under c_x.
            eapply IHΓ; eauto; fold value_subst; fold tm_subst.
            + refinement_solver.
            + eapply basic_typing_subst_tm_post in H4; eauto.
              refinement_solver.
          - mydestr. auto_meet_exists HE.
            auto_meet_reduce. dsimp1. rename x2 into c_x. auto_under x0.
            eapply IHΓ; eauto; fold value_subst; fold tm_subst.
            + refinement_solver.
            + eapply basic_typing_subst_tm_post; eauto.
          - intros. auto_under v_x.
            apply IHΓ; eauto; fold value_subst; fold tm_subst.
            eapply basic_typing_subst_tm_post in H4; eauto. refinement_solver.
Qed.

Lemma inv_rRctx_letapp_oarr: forall Γ st (τ: rty) b n d ϕ x τ_x (v1 v2: value) e,
    x ∉ fv_tm e ∪ rty_fv τ -> not_overbasety τ -> not_overbasety τ_x ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) τ ->
    wf_ctxrR st (Γ ++ [(x, [v:b|n|d|ϕ])]) ->
    wf_ctxrR st (Γ ++ [(x, τ_x ^r^ v2)]) ->
    (⅋{st}⟦-:{v: b | n | d | ϕ}⤑ τ_x⟧{Γ}) v1 ->
    (⅋{st}⟦[v:b|n|d|ϕ]⟧{Γ}) v2 ->
    (⅋{st}⟦τ⟧{Γ ++ [(x, τ_x ^r^ v2)] }) (e ^t^ x) ->
    ⅋{st}⟦τ⟧{Γ ++ [(x, τ_x ^r^ v2)] } (tletapp v1 v2 e).
Proof.
    induction Γ; intros.
    invclear H5. invclear H6. invclear H3; try auto_ty_exfalso.
    eapply rR_letapp_base'; eauto.
    assert ((exists (n: constant), v2 = n) \/ (exists (y: atom), v2 = y)) as Hv2.
    { invclear H6; eapply has_basety_implies_constant_or_var; eauto;
      basic_typing_solver. }
    mydestr.
    assert (a ∉ dom aset st ∪ ctxdom Γ ∪ {[x]}) as Ha.
    { inv_rd_simpl0. apply wf_ctxrR_regular1 in H3; mydestr. refinement_solver. }
    RD_simp2; constructor; auto.
    - denotation_simp. apply cons_basic_typing_drop_last_tm. inv_rd_simpl0.
      eapply tletapp_typable with (x:=x); eauto.
      fast_set_solver. inv_rd_simpl0.
    - intros. auto_under c_x.
      assert (closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) (τ_x ^r^ ({a := c_x }v v2))) as Hclosed.
      { apply closed_rty_subst_var; auto.
        apply inv_ctxrR_regular1 in H17; mydestr; eauto.
        apply ok_dctx_regular in H13; mydestr.
        apply closed_rty_oarr_implies_closed_rty_retty with (c:=c_x) in H20.
        refinement_solver. }
      eapply state_subst_implies_rty_subst_inv_ctxrR_all_open_to_v; eauto.
      apply inv_ctxrR_regular1 in H17; mydestr; eauto.
      simpl. eapply IHΓ; eauto; fold value_subst; fold tm_subst.
      + pose (fv_of_subst_tm a c_x e). set_solver.
      + refinement_solver.
      + eapply state_subst_implies_rty_subst_wf_ctxrR_all_v_to_open; eauto.
      + eapply state_subst_implies_rty_subst_inv_ctxrR_all_v_to_open; eauto.
        rewrite <- subst_open_var_tm; auto; fast_set_solver.
   - denotation_simp. apply cons_basic_typing_drop_last_tm. inv_rd_simpl0.
      eapply tletapp_typable with (x:=x); eauto.
      fast_set_solver. inv_rd_simpl1.
   - mydestr. auto_meet_exists HE.
     auto_meet_reduce. dsimp1. rename x5 into c_x. auto_under x0.
     assert (closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) (τ_x ^r^ ({a := c_x }v v2))) as Hclosed.
      { apply closed_rty_subst_var; auto.
        apply inv_ctxrR_regular1 in H18; mydestr; eauto.
        eapply closed_rty_open_trans. refinement_solver. }
      eapply state_subst_implies_rty_subst_inv_ctxrR_all_open_to_v; eauto.
      apply inv_ctxrR_regular1 in H18; mydestr; eauto.
      simpl. eapply IHΓ; eauto; fold value_subst; fold tm_subst.
      + pose (fv_of_subst_tm a c_x e). set_solver.
      + refinement_solver.
      + eapply state_subst_implies_rty_subst_wf_ctxrR_all_v_to_open; eauto.
      + eapply state_subst_implies_rty_subst_inv_ctxrR_all_v_to_open; eauto.
        rewrite <- subst_open_var_tm; auto; fast_set_solver.
   - denotation_simp. apply cons_basic_typing_drop_last_tm. inv_rd_simpl0.
      eapply tletapp_typable with (x:=x); eauto.
      fast_set_solver. inv_rd_simpl1.
   - intros. auto_under v_x.
     assert (a ∉ stale v2) as Hav.
     { eapply arr_type_in_tyctx_is_free; eauto; basic_typing_solver. }
     simpl. rewrite (subst_fresh_value v2); auto.
     eapply IHΓ; eauto; fold value_subst; fold tm_subst.
     + pose (fv_of_subst_tm a v_x e).
       assert (closed_value v_x). apply rR_implies_no_free_value in H3; auto.
       unfold closed_value in H6.
       rewrite H6 in s. set_solver.
      + simpl in H2. dec_solver2.
      + rewrite (subst_fresh_tm v2) in H22; auto.
      + rewrite <- subst_open_var_tm; auto. fast_set_solver. refinement_solver.
Qed.
