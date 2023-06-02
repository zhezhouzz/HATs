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
From CT Require Import WFCtxDenotationProp.
From CT Require Import InvDenotation.
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

Global Hint Resolve mk_eq_constant_is_not_overbasety: core.
Global Hint Resolve mk_eq_var_is_not_overbasety: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Constructors ok_dctx: core.
Global Hint Resolve rR_implies_no_free: core.
Global Hint Resolve ctxrR_tlete_drop_halt_lhs: core.
Global Hint Resolve rR_implies_reduction_no_free: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Resolve under_not_overbasety: core.

Ltac RD_simp2 :=
  repeat
    (listctx_set_simpl;
     match goal with
     | [H: (⅋{_}⟦ _ ⟧{ [] }) _ |- _ ] => invclear H
     | [|- (⅋{_}⟦ _ ⟧{ [] }) _ ] => constructor
     | [H: (⅋{_}⟦_⟧{ (_, _) :: _ }) _ |- _ ] => invclear H; try auto_ty_exfalso
     | [H: wf_ctxrR _ ((_,_) :: _ ) |- _ ] => invclear H; try auto_ty_exfalso
     end).

Ltac inv_simpl :=
  repeat match goal with
    | [H: ?x ∉ fv_tm ?e, H': context [({?x := _ }t ?e)] |- _ ] =>
        setoid_rewrite (subst_fresh_tm e x) in H'; auto
    | [H: ?x ∉ fv_tm ?e |- context [({?x := _ }t ?e)] ] =>
        setoid_rewrite (subst_fresh_tm e x); auto
    | [H: ?x ∉ rty_fv ?r, H': context [{0;b∅;({?x↦_}) _}⟦_⟧ _] |- _ ] =>
        rewrite rR_shadow_update_st in H'; refinement_solver
    | [H: ?x ∉ rty_fv ?r |- context [{0;b∅;({?x↦_}) _}⟦_⟧ _] ] =>
        rewrite rR_shadow_update_st; refinement_solver
    end.

Lemma inv_implies_ctxrR_drop_last: forall Γ st x τ_x e τ,
    wf_ctxrR st (Γ ++ [(x, τ_x)]) ->
    closed_rty 0 (ctxdom ⦑ Γ ⦒ ∪ dom aset st) τ ->
    x ∉ rty_fv τ -> x ∉ fv_tm e -> not_overbasety τ_x ->
    ⅋{st}⟦τ⟧{Γ ++ [(x, τ_x)] } e ->
    ⅋{st}⟦τ⟧{Γ} e.
Proof.
  induction Γ; intros.
  - RD_simp2; mydestr.
    + auto_under x1. RD_simp2. inv_simpl.
    + assert ({0;b∅;st}⟦ τ_x ⟧ (riv τ_x)) by (apply riv_in_any_under; refinement_solver7).
      auto_under (riv τ_x). RD_simp2. lc_simpl3.
  - RD_simp2.
    + inversion H10; auto_ty_exfalso4; subst. constructor; auto. refinement_solver7.
      denotation_simp. eapply cons_basic_strengthen1_pre_cons_tm; eauto.
      intros. auto_under c_x.
      apply IHΓ in H14; auto. refinement_solver. lc_solver_r.
    + inversion H10; auto_ty_exfalso4; subst. mydestr. constructor; auto. refinement_solver7.
      denotation_simp. eapply cons_basic_strengthen1_pre_cons_tm; eauto.
      auto_meet_exists Hmeet. auto_meet_reduce. auto_under x0.
      apply IHΓ in H11; auto. dsimp1. refinement_solver.
      eapply rR_implies_reduction_no_free in H17; eauto. unfold closed_value in H17.
      lc_solver_r.
    + inversion H11; auto_ty_exfalso4; subst. denotation_simp. constructor; auto. refinement_solver7.
      denotation_simp. eapply cons_basic_strengthen1_pre_cons_tm; eauto.
      intros. auto_under v_x.
      apply IHΓ in H15; auto. apply rR_implies_no_free_value in H.
      lc_solver_r.
Qed.

Lemma wf_implies_ctxrR_tlete_is_arr: forall Γ st x τ_x (e_x: value) e τ,
    wf_ctxrR st (Γ ++ [(x, τ_x)]) ->
    not_overbasety τ -> is_arr τ_x ->
    ⅋{st}⟦τ_x⟧{Γ} e_x ->
    ⅋{st}⟦τ⟧{Γ ++ [(x, τ_x)] } e -> ⅋{st}⟦τ⟧{Γ ++ [(x, τ_x)] } (tlete e_x (x \t\ e)).
Proof.
  induction Γ; intros; RD_simp2.
  - constructor; auto. denotation_simp. eapply tlete_apply_typable_aux3; eauto; refinement_solver7.
    intros. auto_under e_x. RD_simp2.
    lc_simpl3. eapply termR_perserve_rR; eauto; refinement_solver.
    apply termR_let_one_step_from_basic_type'. basic_typing_solver. fast_set_solver.
    eapply tlete_apply_typable_aux; eauto; refinement_solver.
  - constructor; auto. denotation_simp. eapply tlete_apply_typable_aux4; eauto; refinement_solver7.
    intros. auto_under c_x.
    eapply IHΓ in H13; eauto. fold value_subst in H13. lc_simpl3.
    rewrite <- subst_close_tm; auto. refinement_solver. denotation_simp. basic_typing_solver8.
  - constructor; auto. denotation_simp. eapply tlete_apply_typable_aux4; eauto; refinement_solver7.
    mydestr. auto_meet_exists Hmeet. auto_meet_reduce.
    auto_under ({a := v_x }t e_x). eapply IHΓ in H4; eauto. fold value_subst in H4. lc_simpl3.
    rewrite <- subst_close_tm; auto. dsimp1. denotation_simp. basic_typing_solver8.
  - constructor; auto. denotation_simp. eapply tlete_apply_typable_aux4; eauto; refinement_solver7.
    intros. auto_under v_x.
    eapply IHΓ in H18; eauto. fold value_subst in H18. lc_simpl3.
    rewrite <- subst_close_tm; auto. refinement_solver7.
    denotation_simp. basic_typing_solver8.
Qed.

Lemma inv_ctxrR_regular0:
  forall Γ τ st e, ⅋{ st }⟦ τ ⟧{ Γ } e ->
              closed_rty 0 (ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ /\ ok_dctx (dom _ st) Γ.
Proof.
  induction Γ; simpl; intros; invclear H; simpl; auto; dec_solver2.
  - apply rR_regular2 in H0; mydestr. constructor; simpl; auto.
    + closed_rty_solver.
Qed.

Lemma inv_ctxrR_regular1:
  forall Γ τ st e, ⅋{ st }⟦ τ ⟧{ Γ } e ->
              (ok_dctx (dom _ st) Γ) /\
                ctx_closed_rty (dom _ st) Γ /\
                closed_rty 0 (ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ.
Proof.
  intros. apply inv_ctxrR_regular0 in H. mydestr.
  do 2 (split; auto). apply ok_dctx_regular2 in H0; mydestr; auto.
Qed.

Lemma inv_ctxrR_regular2:
  forall Γ τ st e, ⅋{ st }⟦ τ ⟧{ Γ } e -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋.
Proof.
  induction Γ; simpl; intros; invclear H; simpl; auto.
  - apply rR_regular2 in H0; mydestr; auto.
Qed.

Lemma inv_ctxrR_regular:
  forall Γ τ st e, ⅋{ st }⟦ τ ⟧{ Γ } e ->
              ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋ /\
                (ok_dctx (dom _ st) Γ) /\
                ctx_closed_rty (dom _ st) Γ /\
                closed_rty 0 (ctxdom ⦑Γ⦒ ∪ (dom _ st)) τ.
Proof.
  intros. split.
  - eapply inv_ctxrR_regular2; eauto.
  - eapply inv_ctxrR_regular1; eauto.
Qed.

Ltac ok_dctx_simpl1 :=
  repeat
    match goal with
    | [H: wf_ctxrR _ _ |- _ ≡ _ ] => apply wf_ctxrR_regular1 in H; mydestr
    | [H: wf_ctxrR _ _ |- _ ⊆ _ ] => apply wf_ctxrR_regular1 in H; mydestr
    | [H: wf_ctxrR _ _ |- _ ∉ _ ] => apply wf_ctxrR_regular1 in H; mydestr
    | [H: ok_dctx _ _ |- _ ≡ _ ] => apply ok_dctx_regular2 in H; mydestr
    | [H: ok_dctx _ _ |- _ ⊆ _ ] => apply ok_dctx_regular2 in H; mydestr
    | [H: ok_dctx _ _ |- _ ∉ _ ] => apply ok_dctx_regular2 in H; mydestr
    | [H: ok ((_, _) :: _) |- _ ≡ _ ] => rewrite ok_pre_destruct in H; mydestr
    | [H: ok ((_, _) :: _) |- _ ⊆ _ ] => rewrite ok_pre_destruct in H; mydestr
    | [H: ok ((_, _) :: _) |- _ ∉ _ ] => rewrite ok_pre_destruct in H; mydestr
    | [H: ok (_ ++ [(_, _)]) |- _ ≡ _ ] => rewrite ok_post_destruct in H; mydestr
    | [H: ok (_ ++ [(_, _)]) |- _ ⊆ _ ] => rewrite ok_post_destruct in H; mydestr
    | [H: ok (_ ++ [(_, _)]) |- _ ∉ _ ] => rewrite ok_post_destruct in H; mydestr
    end.

Ltac inv_rd_simpl1 :=
  progress repeat
    (ctx_erase_simp;
     listctx_set_simpl;
     ok_dctx_simpl1;
     ctx_rm_simp1;
     my_simplify_map_eq3;
     basic_typing_simpl1;
     repeat match goal with
       | [H: context [ ⌊{_ ~r> _} _ ⌋ ] |- _ ] => rewrite rty_open_perserve_erase in H
       | [|- context [ ⌊{_ ~r> _} _ ⌋ ]] => rewrite rty_open_perserve_erase
       | [H: ⅋{_}⟦_⟧{_} _ |- _ ∉ fv_tm _] => apply inv_ctxrR_regular2 in H; mydestr
       | [H: ⅋{_}⟦_⟧{_} _ |- _ ∉ fv_value _] => apply inv_ctxrR_regular2 in H; mydestr
       | [H: closed_rty _ _ ?τ |- _ ∉ rty_fv ?τ ] => invclear H
       | [H: ⅋{_}⟦_⟧{_} _ |- _ ⊢t _ ⋮t _ ] => apply inv_ctxrR_regular2 in H; mydestr
       | [H: ⅋{_}⟦_⟧{_} _ |- _ ⊢t _ ⋮v _] => apply inv_ctxrR_regular2 in H; mydestr
       end).

Ltac inv_rd_solver1 :=
  inv_rd_simpl1;
  match goal with
  | [H: ?Γ ⊢t ?e ⋮v ?T |- ?x ∉ fv_value ?e] => eapply tyable_implies_fresh_value in H; eauto
  | [H: ?Γ ⊢t ?e ⋮t ?T |- ?x ∉ fv_tm ?e] => eapply tyable_implies_fresh_tm in H; eauto
  end;
  inv_rd_simpl1.

Lemma state_subst_implies_rty_subst_inv_ctxrR_all_v_to_c
    : ∀ (a: atom) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) τ τ' e,
  a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
  closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> c_x} τ) ->
   ⅋{<[a:=c_x]> st}⟦τ'⟧{Γ ++ [(x, {k ~r> a} τ)] } e ->
   ⅋{<[a:=c_x]> st}⟦τ'⟧{Γ ++ [(x, {k ~r> c_x} τ)] } e.
Proof.
  intros a. induction Γ; intros.
  - assert (ok_dctx (dom aset (<[a:=c_x]> st)) [(x, {k ~r> c_x} τ)]) as Hokd.
    { apply inv_ctxrR_regular1 in H1; mydestr.
      eapply state_subst_implies_rty_subst_ok_dctx_all_v_to_c in H1; eauto.
      fast_set_solver. }
    assert (closed_rty 0 (dom aset (<[a:=c_x]> st)) ({k ~r> a} τ)) as Hclosed.
    { apply inv_ctxrR_regular1 in H1; mydestr. unfold ctx_closed_rty in H2.
      assert ([] ++ [(x, {k ~r> a} τ)] = [] ++ [(x, {k ~r> a} τ)] ++ []) as Htmp by listctx_set_simpl.
      apply H2 in Htmp. refinement_solver. }
    listctx_set_simpl.
    destruct τ; invclear H1; try auto_ty_exfalso.
    + constructor; auto. intros.
      rewrite unfold_rty_obase in H1.
      apply state_subst_implies_rty_subst_rR_all_c_to_v in H1; auto.
    + constructor; auto.
      mydestr. exists x0; split; eauto.
      rewrite unfold_rty_ubase. apply state_subst_implies_rty_subst_rR_all_v_to_c; auto.
      refinement_solver.
    + constructor; auto. inv_rd_simpl3. inv_rd_simpl1.
      intros. apply H12.
      apply state_subst_implies_rty_subst_rR_all_c_to_v in H1; auto.
    + constructor; auto. inv_rd_simpl3. inv_rd_simpl1.
      intros. apply H12.
      apply state_subst_implies_rty_subst_rR_all_c_to_v in H1; auto.
 - assert (ok_dctx (dom aset (<[a:=c_x]> st)) ((a0 :: Γ) ++ [(x, {k ~r> c_x} τ)])) as Hokd.
    { apply inv_ctxrR_regular1 in H1; mydestr.
      eapply state_subst_implies_rty_subst_ok_dctx_all_v_to_c in H1; eauto.
      fast_set_solver. }
    assert (closed_rty 0
              (ctxdom  ⦑(a0 :: Γ) ++ [(x, {k ~r> c_x} τ)]⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> a} τ)) as Hclosed.
    { apply inv_ctxrR_regular1 in H1; mydestr. auto. unfold ctx_closed_rty in H2.
      assert (((a0, r) :: Γ) ++ [(x, {k ~r> a} τ)] = ((a0, r) :: Γ) ++ [(x, {k ~r> a} τ)] ++ []) as Htmp by listctx_set_simpl.
      apply H2 in Htmp. refinement_solver. }
   invclear H1.
   + listctx_set_simpl. constructor; auto.
     { inv_rd_simpl1. }
     { inv_rd_simpl1. inv_rd_simpl3. inv_rd_simpl1. }
     intros. auto_under c_x0.
     setoid_rewrite insert_commute in H10; try fast_set_solver.
     setoid_rewrite insert_commute; try fast_set_solver.
     apply IHΓ; refinement_solver.
   + listctx_set_simpl. constructor; auto.
     { inv_rd_simpl1. }
     { inv_rd_simpl1. inv_rd_simpl3. inv_rd_simpl1. }
     mydestr. exists x1; split; eauto.
     intros. auto_under e_x. dsimp1.
     setoid_rewrite insert_commute in H2; try fast_set_solver.
     setoid_rewrite insert_commute; try fast_set_solver.
     apply IHΓ; refinement_solver.
   + listctx_set_simpl. constructor; auto.
     { inv_rd_simpl1. }
     { inv_rd_simpl1. inv_rd_simpl3. inv_rd_simpl1. }
     intros.
     apply IHΓ; refinement_solver.
Qed.

Lemma state_subst_implies_rty_subst_inv_ctxrR_all_c_to_v
    : ∀ (a: atom) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) τ τ' e,
  a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
  closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> a} τ) ->
   ⅋{<[a:=c_x]> st}⟦τ'⟧{Γ ++ [(x, {k ~r> c_x} τ)] } e ->
   ⅋{<[a:=c_x]> st}⟦τ'⟧{Γ ++ [(x, {k ~r> a} τ)] } e.
Proof.
  intros a. induction Γ; intros.
  - assert (ok_dctx (dom aset (<[a:=c_x]> st)) [(x, {k ~r> a} τ)]) as Hokd.
    { apply inv_ctxrR_regular1 in H1; mydestr.
      eapply state_subst_implies_rty_subst_ok_dctx_all_c_to_v in H1; eauto.
      fast_set_solver. }
    assert (closed_rty 0 (dom aset (<[a:=c_x]> st)) ({k ~r> c_x} τ)) as Hclosed.
    { apply inv_ctxrR_regular1 in H1; mydestr. unfold ctx_closed_rty in H2.
      assert ([] ++ [(x, {k ~r> c_x} τ)] = [] ++ [(x, {k ~r> c_x} τ)] ++ []) as Htmp by listctx_set_simpl.
      apply H2 in Htmp. refinement_solver. }
    listctx_set_simpl.
    destruct τ; invclear H1; try auto_ty_exfalso.
    + constructor; auto. intros.
      rewrite unfold_rty_obase in H1.
      apply state_subst_implies_rty_subst_rR_all_v_to_c in H1; auto.
    + constructor; auto.
      mydestr. exists x0; split; eauto.
      rewrite unfold_rty_ubase. apply state_subst_implies_rty_subst_rR_all_c_to_v; auto.
      refinement_solver.
    + constructor; auto. inv_rd_simpl3. inv_rd_simpl1.
      intros. apply H12.
      apply state_subst_implies_rty_subst_rR_all_v_to_c in H1; auto.
    + constructor; auto. inv_rd_simpl3. inv_rd_simpl1.
      intros. apply H12.
      apply state_subst_implies_rty_subst_rR_all_v_to_c in H1; auto.
 - assert (ok_dctx (dom aset (<[a:=c_x]> st)) ((a0 :: Γ) ++ [(x, {k ~r> a} τ)])) as Hokd.
    { apply inv_ctxrR_regular1 in H1; mydestr.
      eapply state_subst_implies_rty_subst_ok_dctx_all_c_to_v in H1; eauto.
      fast_set_solver. }
    assert (closed_rty 0
              (ctxdom  ⦑(a0 :: Γ) ++ [(x, {k ~r> c_x} τ)]⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> a} τ)) as Hclosed.
    { apply inv_ctxrR_regular1 in H1; mydestr. auto. unfold ctx_closed_rty in H2.
      assert (((a0, r) :: Γ) ++ [(x, {k ~r> c_x} τ)] = ((a0, r) :: Γ) ++ [(x, {k ~r> c_x} τ)] ++ []) as Htmp by listctx_set_simpl.
      apply H2 in Htmp. refinement_solver. }
   invclear H1.
   + listctx_set_simpl. constructor; auto.
     { inv_rd_simpl1. }
     { inv_rd_simpl1. inv_rd_simpl3. inv_rd_simpl1. }
     intros. auto_under c_x0.
     setoid_rewrite insert_commute in H10; try fast_set_solver.
     setoid_rewrite insert_commute; try fast_set_solver.
     apply IHΓ; refinement_solver.
   + listctx_set_simpl. constructor; auto.
     { inv_rd_simpl1. }
     { inv_rd_simpl1. inv_rd_simpl3. inv_rd_simpl1. }
     mydestr. exists x1; split; eauto.
     intros. auto_under e_x. dsimp1.
     setoid_rewrite insert_commute in H2; try fast_set_solver.
     setoid_rewrite insert_commute; try fast_set_solver.
     apply IHΓ; refinement_solver.
   + listctx_set_simpl. constructor; auto.
     { inv_rd_simpl1. }
     { inv_rd_simpl1. inv_rd_simpl3. inv_rd_simpl1. }
     intros.
     apply IHΓ; refinement_solver.
Qed.

Lemma state_subst_implies_rty_subst_inv_ctxrR_all_open_to_v
  : ∀ (a: atom) (v: value) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) τ τ' e,
    ((exists (n: constant), v = n) \/ (exists (y: atom), v = y)) ->
    a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> v} τ) ->
    ⅋{<[a:=c_x]> st}⟦τ'⟧{Γ ++ [(x, {k ~r> {a := c_x}v v} τ)] } e ->
    ⅋{<[a:=c_x]> st}⟦τ'⟧{Γ ++ [(x, {k ~r> v} τ)] } e.
Proof.
  intros. destruct H; mydestr; subst; auto.
  destruct (decide (a = x0)); subst; auto.
  - simpl in H2. rewrite decide_True in H2; auto.
    eapply state_subst_implies_rty_subst_inv_ctxrR_all_c_to_v; auto.
  - simpl in H2. dec_solver2.
Qed.

Lemma state_subst_implies_rty_subst_inv_ctxrR_all_v_to_open
  : ∀ (a: atom) (v: value) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) τ τ' e,
    ((exists (n: constant), v = n) \/ (exists (y: atom), v = y)) ->
    a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> {a := c_x}v v} τ) ->
    ⅋{<[a:=c_x]> st}⟦τ'⟧{Γ ++ [(x, {k ~r> v} τ)] } e ->
    ⅋{<[a:=c_x]> st}⟦τ'⟧{Γ ++ [(x, {k ~r> {a := c_x}v v} τ)] } e.
Proof.
  intros. destruct H; mydestr; subst; auto.
  destruct (decide (a = x0)); subst; auto.
  - simpl in H1. rewrite decide_True in H1; auto.
    simpl. rewrite decide_True; auto.
    eapply state_subst_implies_rty_subst_inv_ctxrR_all_v_to_c; auto.
  - dec_solver2.
Qed.

Lemma inv_rRctx_oarr: forall Γ st (τ: rty) x b n d ϕ τ e,
    x ∉ fv_tm e -> x ∉ rty_fv τ ->
    wf_ctxrR st (Γ ++ [(x, {v:b|n|d|ϕ})]) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom _ st) (-:{v: b | n | d | ϕ}⤑ τ) ->
    ⅋{st}⟦τ ^r^ x⟧{Γ ++ [(x, {v:b|n|d|ϕ})] } (e ^t^ x) ->
    ⅋{st}⟦-:{v: b | n | d | ϕ}⤑ τ⟧{Γ} (vlam b e).
Proof.
  induction Γ; intros; RD_simp2; inv_rd_simpl1.
  - invclear H6; auto_ty_exfalso. do 2 constructor.
    + eapply opened_term_tyable_renaming; eauto.
    + apply (closed_rty_trans _ (ctxdom ⦑[]⦒ ∪ dom aset st)); eauto. fast_set_solver.
    + exists (vlam b e). split; auto.
      { apply multistep_refl. rewrite lc_abs_iff_body.
        eapply lc_fresh_var_implies_body; basic_typing_solver. }
      intros.
      assert (({0;b∅;st}⟦{v:b|n|d|ϕ}⟧) c_x).
      { do 2 constructor. refinement_solver. refinement_solver.
        eexists; split; eauto. }
      auto_under c_x. RD_simp2. rewrite open_subst_same_tm in H6; auto.
      rewrite denotation_st_update_iff_subst in H6; mydestr; try fast_set_solver.
      rewrite open_subst_same_rty in H8; auto.
      assert (({0;b∅;st}⟦τ0 ^r^ c_x⟧) (mk_app (vlam b e) c_x)).
      { eapply termR_perserve_rR; eauto. rewrite rty_open_perserve_not_overbasety. refinement_solver.
        refinement_solver.
        apply mk_app_reduce_to_open'; refinement_solver. inv_rd_simpl1.
      eapply opened_term_tyable_renaming; eauto. }
      rewrite closed_rty_destruct_oarr in H2; mydestr.
      apply rR_open_trans_empty; auto. refinement_solver.
      refinement_solver.
  - invclear H9; auto_ty_exfalso. constructor; auto.
    + refinement_solver.
    + simpl. constructor; auto. eapply opened_term_tyable_renaming; eauto.
    + intros. auto_under c_x. rewrite subst_open_var_tm in H13; auto.
      eapply IHΓ in H13; eauto.
      pose (fv_of_subst_tm a c_x e). set_solver.
      apply (closed_rty_trans _ ({[a]} ∪ ctxdom ⦑Γ⦒ ∪ dom aset st)); eauto. fast_set_solver.
      refinement_solver.
  - invclear H8; auto_ty_exfalso. constructor; auto.
    + refinement_solver.
    + simpl. constructor; auto. eapply opened_term_tyable_renaming; eauto.
    + mydestr. auto_meet_exists Hmeet. auto_meet_reduce. auto_under x0.
      rewrite subst_open_var_tm in H8; auto.
      eapply IHΓ in H8; eauto. dsimp1.
      pose (fv_of_subst_tm a x3 e). set_solver.
      apply (closed_rty_trans _ ({[a]} ∪ ctxdom ⦑Γ⦒ ∪ dom aset st)); eauto. dsimp1.
      refinement_solver. op_solver1. op_solver1.
  - invclear H10; auto_ty_exfalso. constructor; auto.
    + refinement_solver.
    + simpl. constructor; auto. eapply opened_term_tyable_renaming; eauto.
    + intros. auto_under v_x.
      rewrite subst_open_var_tm in H14; auto.
      eapply IHΓ in H14; eauto.
      pose (fv_of_subst_tm a v_x e).
      assert (fv_value v_x ≡ ∅).
      match goal with
      | [H: {0;b∅;?st}⟦?r⟧ (tvalue ?v_x) |- closed_value ?v_x ] =>
          apply rR_regular2 in H; mydestr; basic_typing_solver
      | [H: {0;b∅;?st}⟦?r⟧ (tvalue ?v_x) |- fv_value ?v_x ≡ ∅ ] =>
          apply rR_regular2 in H; mydestr; basic_typing_solver
      end.
      set_solver.
      refinement_solver. refinement_solver.
Qed.

Lemma inv_rRctx_arrarr: forall Γ st (τ: rty) x τ1 τ2 τ e,
    x ∉ fv_tm e -> x ∉ rty_fv τ ->
    wf_ctxrR st (Γ ++ [(x, τ1 ⤑ τ2)]) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom _ st) ((τ1 ⤑ τ2) ⤑ τ) ->
    ⅋{st}⟦τ⟧{Γ ++ [(x, τ1 ⤑ τ2)] } (e ^t^ x) ->
    ⅋{st}⟦(τ1 ⤑ τ2)⤑ τ⟧{Γ} (vlam ⌊τ1 ⤑ τ2⌋ e).
Proof.
  induction Γ; intros; RD_simp2.
  - clear H11. invclear H10; auto_ty_exfalso. do 2 constructor.
    + eapply opened_term_tyable_renaming; eauto.
    + auto_dclosed_rty. split; auto. refinement_solver.
    + exists (vlam ⌊τ1 ⤑ τ2⌋ e). split; auto.
      { apply multistep_refl. rewrite lc_abs_iff_body.
        eapply lc_fresh_var_implies_body; basic_typing_solver. }
      intros. auto_under v_x. RD_simp2. rewrite open_subst_same_tm in H4; auto.
      rewrite closed_rty_destruct_arrarr in H2; mydestr.
      eapply termR_perserve_rR; eauto. refinement_solver. simpl.
      apply mk_app_reduce_to_open'; refinement_solver.
      eapply opened_term_tyable_renaming; eauto.
  - invclear H9; auto_ty_exfalso. constructor; auto.
    + refinement_solver.
    + inv_rd_simpl1. constructor; auto. eapply opened_term_tyable_renaming; eauto.
    + intros. auto_under c_x. rewrite subst_open_var_tm in H13; auto.
      eapply IHΓ in H13; eauto.
      pose (fv_of_subst_tm a c_x e). set_solver.
      apply (closed_rty_trans _ ({[a]} ∪ ctxdom ⦑Γ⦒ ∪ dom aset st)); eauto. fast_set_solver.
      refinement_solver.
  - invclear H8; auto_ty_exfalso. constructor; auto.
    + refinement_solver.
    + inv_rd_simpl1. constructor; auto. eapply opened_term_tyable_renaming; eauto.
    + mydestr. auto_meet_exists Hmeet. auto_meet_reduce. auto_under x0.
      rewrite subst_open_var_tm in H8; auto.
      eapply IHΓ in H8; eauto. dsimp1.
      pose (fv_of_subst_tm a x3 e). set_solver.
      apply (closed_rty_trans _ ({[a]} ∪ ctxdom ⦑Γ⦒ ∪ dom aset st)); eauto. dsimp1.
      refinement_solver. op_solver1. op_solver1.
  - invclear H10; auto_ty_exfalso. constructor; auto.
    + inv_rd_simpl1.
    + refinement_solver.
    + inv_rd_simpl1. constructor; auto. eapply opened_term_tyable_renaming; eauto.
    + inv_rd_simpl1. intros. auto_under v_x.
      rewrite subst_open_var_tm in H14; auto.
      eapply IHΓ in H14; eauto.
      pose (fv_of_subst_tm a v_x e).
      assert (fv_value v_x ≡ ∅) by refinement_solver. set_solver.
      refinement_solver. refinement_solver.
Qed.

Lemma inv_rRctx_pre_weakening_empty: forall Γ st τ,
    not_overbasety τ ->
    wf_ctxrR st Γ ->
    (forall e, {st}⟦τ⟧ e -> ⅋{st}⟦τ⟧{Γ} e).
Proof.
  induction Γ; intros; RD_simp2; denotation_simp.
  - invclear H5; auto_ty_exfalso. constructor; refinement_solver7.
    intros. apply IHΓ; auto. lc_simpl3.
    rewrite rR_shadow_update_st_c; refinement_solver.
  - constructor; refinement_solver7. mydestr. auto_meet_exists Hmeet.
    apply IHΓ; eauto.
    rewrite rR_shadow_update_st; refinement_solver.
    auto_under x. lc_simpl3.
  - constructor; refinement_solver7. intros. lc_simpl3.
Qed.

Lemma inv_rRctx_pre_weakening: forall Γ1 Γ2 st τ,
    not_overbasety τ ->
    wf_ctxrR st (Γ1 ++ Γ2) ->
    (forall e, ⅋{st}⟦τ⟧{Γ1} e -> ⅋{st}⟦τ⟧{Γ1 ++ Γ2} e).
Proof.
  induction Γ1; intros; RD_simp2; denotation_simp.
  - apply inv_rRctx_pre_weakening_empty; auto.
  - constructor; refinement_solver. ctx_erase_simp5. basic_typing_solver8. ctx_erase_simp5.
  - constructor; auto. refinement_solver. ctx_erase_simp5. basic_typing_solver7. ctx_erase_simp5.
    auto_meet_exists Hmeet. auto_meet_reduce.
  - constructor; auto. refinement_solver. ctx_erase_simp5. basic_typing_solver7. ctx_erase_simp5.
Qed.

Lemma wf_ctxrR_implies_inv_var_is_arr_last: forall (Γ: listctx rty) st x τ_x,
    is_arr τ_x -> closed_rty 0 (ctxdom ⦑ Γ ⦒ ∪ dom _ st) τ_x ->
    wf_ctxrR st (Γ ++ [(x, τ_x)]) -> (⅋{st}⟦τ_x⟧{(Γ ++ [(x, τ_x)])}) x.
Proof.
  induction Γ; simpl; intros; mydestr.
  - RD_simp2. constructor; auto.
    + constructor; auto. constructor; auto. refinement_solver. simpl. var_dec_solver.
    + intros. RD_simp2. lc_simpl3. var_dec_solver.
  -  assert (x <> a).
     { apply wf_ctxrR_regular1 in H1. apply ok_dctx_regular in H1; mydestr. basic_typing_solver. }
     RD_simp2; simpl in H0.
    + constructor; auto. inv_rd_simpl1. refinement_solver.
      apply var_last_typable. denotation_simp.
      intros. auto_under c_x. lc_simpl3. var_dec_solver. apply IHΓ; auto. refinement_solver.
    + mydestr.
      constructor; auto. refinement_solver. apply var_last_typable. denotation_simp.
      auto_meet_exists Hmeet. auto_under x0.
      lc_simpl3. var_dec_solver. apply IHΓ; auto. dsimp1. refinement_solver.
    + constructor; auto. refinement_solver. apply var_last_typable. denotation_simp.
      intros. lc_simpl3. var_dec_solver. apply IHΓ; auto. dec_solver2.
Qed.

Lemma wf_ctxrR_implies_inv_var_over_last: forall (Γ: listctx rty) st x b n d ϕ,
    wf_ctxrR st (Γ ++ [(x, {v:b|n|d|ϕ})]) -> (⅋{st}⟦ mk_eq_var b x ⟧{(Γ ++ [(x, {v:b|n|d|ϕ})])}) x.
Proof.
  induction Γ; simpl; intros; mydestr.
  - RD_simp2. pose (closed_rty_mk_eq_var b x). constructor; auto.
    + refinement_solver.
    + constructor; auto. constructor; auto. refinement_solver. simpl. var_dec_solver.
    + intros. RD_simp2. lc_simpl3. var_dec_solver. invclear H; mydestr; subst.
      do 2 (split; auto). denotation_simp. refinement_solver.
      intros. my_simplify_map_eq3.
  - pose (closed_rty_mk_eq_var b x).
    assert (x <> a).
    { apply wf_ctxrR_regular1 in H. apply ok_dctx_regular in H; mydestr. basic_typing_solver. }
     RD_simp2; simpl in H0.
    + constructor; auto. inv_rd_simpl1. refinement_solver.
      simpl. apply var_last_typable; denotation_simp.
      intros. auto_under c_x. lc_simpl3. var_dec_solver.
    + mydestr.
      constructor; auto. refinement_solver. simpl. apply var_last_typable. denotation_simp.
      auto_meet_exists Hmeet. auto_under x0.
      lc_simpl3. var_dec_solver.
    + constructor; auto. refinement_solver. simpl. apply var_last_typable; denotation_simp.
      intros. lc_simpl3. var_dec_solver.
Qed.

Lemma wf_ctxrR_implies_inv_var_under_last: forall (Γ: listctx rty) st x b n d ϕ,
    wf_ctxrR st (Γ ++ [(x, [v:b|n|d|ϕ])]) -> (⅋{st}⟦ mk_eq_var b x ⟧{(Γ ++ [(x, [v:b|n|d|ϕ])])}) x.
Proof.
  induction Γ; simpl; intros; mydestr.
  - RD_simp2. mydestr. pose (closed_rty_mk_eq_var b x). constructor; auto.
    + refinement_solver.
    + constructor; auto. constructor; auto. refinement_solver. simpl. var_dec_solver.
    + auto_meet_exists Hmeet. auto_under x0. dsimp1. RD_simp2. var_dec_solver. simpl.
      do 2 (split; auto). denotation_simp. refinement_solver.
      intros. my_simplify_map_eq3.
  - pose (closed_rty_mk_eq_var b x).
    assert (x <> a).
    { apply wf_ctxrR_regular1 in H. apply ok_dctx_regular in H; mydestr. basic_typing_solver. }
     RD_simp2; simpl in H0.
    + constructor; auto. inv_rd_simpl1. refinement_solver.
      simpl. apply var_last_typable; denotation_simp.
      intros. auto_under c_x. lc_simpl3. var_dec_solver.
    + mydestr.
      constructor; auto. refinement_solver. simpl. apply var_last_typable; denotation_simp.
      auto_meet_exists Hmeet. auto_under x0.
      lc_simpl3. var_dec_solver.
    + constructor; auto. refinement_solver. simpl. apply var_last_typable; denotation_simp.
      intros. lc_simpl3. var_dec_solver.
Qed.

Lemma wf_implies_ctxrR_tlete_is_arr_drop: forall Γ st x τ_x (e_x: value) e τ,
    wf_ctxrR st (Γ ++ [(x, τ_x)]) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom _ st) τ ->
    not_overbasety τ -> is_arr τ_x ->
    ⅋{st}⟦τ_x⟧{Γ} e_x ->
    ⅋{st}⟦τ⟧{Γ ++ [(x, τ_x)] } e -> ⅋{st}⟦τ⟧{Γ} (tlete e_x (x \t\ e)).
Proof.
  intros. eapply wf_implies_ctxrR_tlete_is_arr in H4; eauto.
  eapply inv_implies_ctxrR_drop_last; eauto.
  - inv_rd_simpl1. assert (x ∉ ctxdom ⦑Γ⦒); ctx_erase_simp. set_solver.
  - assert (x ∉ fv_value e_x). inv_rd_solver1.
    assert (x ∉ fv_tm (x \t\ e)) by apply close_rm_fv_tm.
    set_solver.
Qed.

Lemma wf_implies_ctxrR_tlete_ubase: forall Γ st x b n d ϕ e_x e τ,
    wf_ctxrR st (Γ ++ [(x, [v:b|n|d|ϕ] )]) ->
    not_overbasety τ ->
    ⅋{st}⟦ [v:b|n|d|ϕ] ⟧{Γ} e_x ->
    ⅋{st}⟦τ⟧{Γ ++ [(x, [v:b|n|d|ϕ] )] } e -> ⅋{st}⟦τ⟧{Γ ++ [(x, [v:b|n|d|ϕ] )] } (tlete e_x (x \t\ e)).
Proof.
  induction Γ; intros; RD_simp2.
  - constructor; auto. denotation_simp. eapply tlete_apply_typable_aux3; eauto; refinement_solver.
    mydestr. auto_meet_exists Hmeet. auto_meet_reduce. auto_under e_x. RD_simp2.
    lc_simpl3. assert ([] ⊢t v_x ⋮v b) by refinement_solver.
    assert (({0;b∅;({x↦v_x}) st}⟦τ⟧) (tlete v_x (x \t\ e))).
    eapply termR_perserve_rR; eauto; refinement_solver.
    apply termR_let_one_step_from_basic_type'. basic_typing_solver. fast_set_solver.
    eapply tlete_apply_typable_aux; eauto; refinement_solver.
    eapply termR_perserve_rR; eauto; refinement_solver.
    eapply termR_elete; eauto.
    eapply reduction_implies_termR; eauto. refinement_solver.
  - constructor; auto. denotation_simp. eapply tlete_apply_typable_aux4; eauto; refinement_solver.
    intros. auto_under c_x.
    eapply IHΓ in H12; eauto. lc_simpl3.
    rewrite <- subst_close_tm; auto. refinement_solver.
    denotation_simp; basic_typing_solver8.
  - constructor; auto. denotation_simp. eapply tlete_apply_typable_aux4; eauto; refinement_solver.
    mydestr. auto_meet_exists Hmeet. auto_meet_reduce.
    auto_under ({a := v_x }t e_x). eapply IHΓ in H3; eauto. lc_simpl3.
    rewrite <- subst_close_tm; auto. dsimp1.
    denotation_simp; basic_typing_solver8.
  - constructor; auto. denotation_simp. eapply tlete_apply_typable_aux4; eauto; refinement_solver.
    intros. auto_under v_x.
    eapply IHΓ in H18; eauto. lc_simpl3.
    rewrite <- subst_close_tm; auto. refinement_solver.
    denotation_simp; basic_typing_solver8.
Qed.

Lemma wf_implies_ctxrR_tlete_ubase_drop: forall Γ st x b n d ϕ e_x e τ,
    wf_ctxrR st (Γ ++ [(x, [v:b|n|d|ϕ] )]) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom _ st) τ ->
    not_overbasety τ ->
    ⅋{st}⟦ [v:b|n|d|ϕ] ⟧{Γ} e_x ->
    ⅋{st}⟦τ⟧{Γ ++ [(x, [v:b|n|d|ϕ] )] } e -> ⅋{st}⟦τ⟧{Γ} (tlete e_x (x \t\ e)).
Proof.
  intros. eapply wf_implies_ctxrR_tlete_ubase in H3; eauto.
  eapply inv_implies_ctxrR_drop_last; eauto.
  - inv_rd_simpl1. assert (x ∉ ctxdom ⦑Γ⦒); ctx_erase_simp. set_solver.
  - assert (x ∉ fv_tm e_x). inv_rd_solver1.
    assert (x ∉ fv_tm (x \t\ e)) by apply close_rm_fv_tm.
    set_solver.
Qed.

Lemma tletbiop_typable: forall op (v1 v2: value) e (x: atom) T,
    x ∉ fv_tm e ->
    [(x, TBase (ret_ty_of_op op))] ⊢t (e ^t^ x) ⋮t T ->
    [] ⊢t v1 ⋮v (fst_ty_of_op op) ->
    [] ⊢t v2 ⋮v (snd_ty_of_op op) ->
    [] ⊢t tletbiop op v1 v2 e ⋮t T.
Proof.
  intros.
  econstructor; eauto. instantiate (1:= {[x]}). intros. listctx_set_simpl.
  assert ( ([] ++ [(x, TBase (ret_ty_of_op op))]) ⊢t e ^t^ x ⋮t T) as Hz; auto.
  apply basic_has_type_renaming with (x0:=x0) in Hz; try listctx_set_solver.
  rewrite open_subst_same_tm in Hz; auto.
Qed.

Lemma tletbiop_typable_ctx: forall Γ op (v1 v2: value) e (x: atom) T,
    x ∉ fv_tm e ->
    (Γ ++ [(x, TBase (ret_ty_of_op op))]) ⊢t (e ^t^ x) ⋮t T ->
    Γ ⊢t v1 ⋮v (fst_ty_of_op op) ->
    Γ ⊢t v2 ⋮v (snd_ty_of_op op) ->
    Γ ⊢t tletbiop op v1 v2 e ⋮t T.
Proof.
  intros. auto_exists_L; intros.
  apply basic_has_type_renaming with (x0:=x0) in H0; try basic_typing_solver.
  rewrite open_subst_same_tm in H0; auto.
Qed.

Lemma tletbiop_typable_ctx_dummy: forall Γ op (v1 v2: value) e (x: atom) T,
    x ∉ fv_tm e ->
    (Γ ++ [(x, TBase (ret_ty_of_op op))]) ⊢t (e ^t^ x) ⋮t T ->
    Γ ⊢t v1 ⋮v (fst_ty_of_op op) ->
    Γ ⊢t v2 ⋮v (snd_ty_of_op op) ->
    (Γ ++ [(x, TBase (ret_ty_of_op op))]) ⊢t tletbiop op v1 v2 e ⋮t T.
Proof.
  intros. assert (Γ ⊢t tletbiop op v1 v2 e ⋮t T).
  eapply tletbiop_typable_ctx; eauto. basic_typing_solver.
Qed.

Lemma tletbiop_typable_ctx_dummy_cons: forall a Ta Γ op (v1 v2: value) e (x: atom) T,
    x ∉ fv_tm e ->
    ((a, Ta) :: Γ ++ [(x, TBase (ret_ty_of_op op))]) ⊢t (e ^t^ x) ⋮t T ->
    ((a, Ta) :: Γ) ⊢t v1 ⋮v (fst_ty_of_op op) ->
    ((a, Ta) :: Γ) ⊢t v2 ⋮v (snd_ty_of_op op) ->
    ((a, Ta) :: Γ ++ [(x, TBase (ret_ty_of_op op))]) ⊢t tletbiop op v1 v2 e ⋮t T.
Proof.
  intros. assert (((a, Ta) :: Γ) ⊢t tletbiop op v1 v2 e ⋮t T).
  eapply tletbiop_typable_ctx; eauto. basic_typing_solver. listctx_set_simpl. basic_typing_solver.
Qed.

Ltac inv_rd_simpl2 :=
  repeat match goal with
    | [H: ⅋{_}⟦_⟧{_} _ |- _ ⊢t _ ⋮t _ ] => apply inv_ctxrR_regular2 in H; mydestr
    | [H: ⅋{_}⟦_⟧{_} _ |- _ ⊢t _ ⋮v _] => apply inv_ctxrR_regular2 in H; mydestr
    end.

Lemma letapp_eval_op_under_bound_tm_termR: forall op (v1 v2: nat) (v_x: value) (x:atom) e T,
    x ∉ fv_tm e ->
    eval_op_under_bound_tm op v1 v2 ↪* v_x ->
    [(x, TBase (ret_ty_of_op op))] ⊢t (e ^t^ x) ⋮t T ->
    [] ⊢t (e ^t^ v_x) ⋮t T ->
    (e ^t^ v_x) <-<{ []; T} (tletbiop op v1 v2 e).
Proof.
  intros. assert ([] ⊢t tletbiop op v1 v2 e ⋮t T) as Ht.
  { econstructor; eauto. destruct op; auto. instantiate (1:= {[x]}). intros. listctx_set_simpl.
    assert ( ([] ++ [(x, TBase (ret_ty_of_op op))]) ⊢t e ^t^ x ⋮t T) as Hz; auto.
    apply basic_has_type_renaming with (x0:=x0) in Hz; try listctx_set_solver.
    rewrite open_subst_same_tm in Hz; auto. }
  constructor; auto. unfold termRraw. intros. invclear H3. simpl in H4. simpl.
  assert ([] ⊢t (eval_op_under_bound_tm op v1 v2) ⋮t ret_ty_of_op op) as Htmp; auto.
  assert ([] ⊢t v_x ⋮t ret_ty_of_op op). eapply multi_preservation; eauto.
  invclear H3. invclear H7; listctx_set_simpl.
  rewrite letbiop_step_spec. do 6 eexists; eauto.
  assert (lc (tletbiop op v1 v2 e)) by basic_typing_solver.
  rewrite letbiop_lc_body in H5; mydestr; auto.
Qed.
