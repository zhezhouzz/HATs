From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.
From CT Require Import RefinementType.
From CT Require Import RefinementTypeTac.
From CT Require Import RefinementTypeDenotation.
From CT Require Import RefinementTypeDenotationTac.
From CT Require Import RefinementTypeDenotationProp.
From CT Require Import WFCtxDenotation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import OperationalSemanticsProp.
Import BasicTyping.
Import TermOrdering.
Import SyntaxSugar.
Import RefinementType.
Import RefinementTypeTac.
Import RefinementTypeDenotation.
Import RefinementTypeDenotationTac.
Import RefinementTypeDenotationProp.
Import WFCtxDenotation.

Lemma wf_ctxrR_iff_wf_ctxrR_not_terr: forall (Γ: listctx rty) st, wf_ctxrR st Γ <-> wf_ctxrR_not_terr st Γ.
Proof.
  induction Γ; split; intros.
  - constructor; auto.
  - constructor; auto.
  - invclear H.
    + constructor; auto. intros. rewrite <- IHΓ; auto.
    + mydestr. constructor; auto. simpl; auto. intro Hf. apply H4 in Hf. mydestr. reduction_simpl1.
      mydestr. exists x0. split; auto.
      intros. rewrite <- IHΓ; eauto.
    + constructor; auto.
      assert ({0;b∅;st}⟦τ_x⟧ (random_inhabitant τ_x)).
      apply random_inhabitant_in_any_under; refinement_solver7.
      eexists; split; eauto. intros. rewrite <- IHΓ; eauto. erewrite state_insert_closed_value_arr; eauto.
      refinement_solver.
  - invclear H. constructor; auto. intros. rewrite IHΓ; auto.
    + mydestr.
      assert (∀ e_wf : tm, ({0;b∅;st}⟦[v:b|n|d|ϕ]⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) as Hv.
      intros. eapply not_rR_inhabitant_err_implies_halt in H1; eauto; refinement_solver.
      constructor; auto.
      exists x0. split; auto. intros. auto_under x0. rewrite IHΓ; auto.
    + mydestr. apply rR_arr_halt in H; eauto.
      constructor; auto.
      { intros. apply rR_arr_halt in H1; eauto. mydestr. eauto. }
      mydestr. auto_under x1. erewrite state_insert_closed_value_arr in H0; eauto.
      rewrite IHΓ; eauto. apply H0. apply multistep_refl. op_solver1. refinement_solver.
Qed.

Lemma is_arr_simpl_rewrite_wf_ctxrR: forall r a st Γ,
    is_arr r ->
    closed_rty 0 (dom aset st) r ->
    (∀ e_wf : tm, ({0;b∅;st}⟦r⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) ->
    (∃ e_x_hat : tm, ({0;b∅;st}⟦r⟧) e_x_hat
                     ∧ (∀ e_x : tm, ({0;b∅;st}⟦r⟧) e_x → ∀ v_x : value, e_x_hat ↪* v_x →
                                                                        wf_ctxrR ({a↦v_x} st) Γ)) <->
      (∀ e_x : tm, ({0;b∅;st}⟦r⟧) e_x → wf_ctxrR st Γ).
Proof.
  intros.
  eapply is_arr_simpl_rewrite with (P:= fun st _ => wf_ctxrR st Γ) in H1; eauto.
Qed.

Lemma wf_ctxrR_implies_ok: forall Γ, wf_ctxrR ∅ Γ -> ok Γ.
Proof.
  induction Γ; intros; auto.
  invclear H; refinement_solver7.
Qed.

Global Hint Resolve wf_ctxrR_implies_ok: core.

Lemma wf_ctxrR_regular1: ∀ (st: state) (Γ: listctx rty), wf_ctxrR st Γ → ok_dctx (dom _ st) Γ.
Proof.
  intros st Γ Hwf. induction Hwf; auto.
Qed.

Ltac wf_regular_solver :=
  match goal with
  | [H: wf_ctxrR ?st ?Γ |- ok_dctx _ ?Γ] => apply wf_ctxrR_regular1 in H; auto
  end.

Lemma ok_dctx_weaken: forall Γ1 Γ2 d, ok_dctx d (Γ1 ++ Γ2) -> ok_dctx d Γ1.
Proof.
  induction Γ1; simpl; intros; mydestr; auto.
  invclear H.
  - constructor; eauto; listctx_set_simpl; try fast_set_solver.
  - apply ok_dctx_cons_arr; eauto; listctx_set_simpl; try fast_set_solver.
Qed.

Lemma wf_ctxrR_weaken: forall Γ1 Γ2 st, wf_ctxrR st (Γ1 ++ Γ2) -> wf_ctxrR st Γ1.
Proof.
  induction Γ1; simpl; intros; mydestr; auto. constructor.
  invclear H. invclear H3; auto_ty_exfalso.
  - constructor; eauto. apply ok_dctx_weaken with (Γ2:=Γ2). listctx_set_simpl.
  - mydestr. constructor; eauto. apply ok_dctx_weaken with (Γ2:=Γ2). listctx_set_simpl.
  - constructor; eauto. apply ok_dctx_weaken with (Γ2:=Γ2). listctx_set_simpl.
Qed.

Lemma wf_ctxrR_implies_inner_closed_rty: forall Γ1 x τ_x Γ2 st,
    wf_ctxrR st (Γ1 ++ (x, τ_x) :: Γ2) -> closed_rty 0 (ctxdom ⦑Γ1⦒ ∪ dom aset st) τ_x.
Proof.
  induction Γ1; simpl; intros; mydestr; auto.
  - invclear H; refinement_solver.
    + invclear H3; refinement_solver.
    + invclear H5; refinement_solver.
  - invclear H; refinement_solver.
    + apply ok_dctx_regular2 in H3; mydestr.
      assert ((a, {v:B|n|d|ϕ}) :: Γ1 ++ (x, τ_x) :: Γ2 = ((a, {v:B|n|d|ϕ}) :: Γ1) ++ [(x, τ_x)] ++ Γ2) as Hz by listctx_set_simpl.
      apply H in Hz. inv_rd_simpl0.
    + apply ok_dctx_regular2 in H4; mydestr.
      assert ((a, [v:B|n|d|ϕ]) :: Γ1 ++ (x, τ_x) :: Γ2 = ((a, [v:B|n|d|ϕ]) :: Γ1) ++ [(x, τ_x)] ++ Γ2) as Hz by listctx_set_simpl.
      apply H2 in Hz. inv_rd_simpl0.
    + apply ok_dctx_regular2 in H5; mydestr.
      assert ((a, r) :: Γ1 ++ (x, τ_x) :: Γ2 = ((a, r) :: Γ1) ++ [(x, τ_x)] ++ Γ2) as Hz by listctx_set_simpl.
      apply H in Hz. dec_solver2. inv_rd_simpl0.
Qed.

Lemma state_subst_implies_rty_subst_wf_ctxrR_all_v_to_c
    : ∀ (a: atom) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) τ,
  a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
  closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> c_x} τ) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> a} τ)]) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> c_x} τ)]).
Proof.
  intros a. induction Γ; intros.
  - assert (ok_dctx (dom aset (<[a:=c_x]> st)) [(x, {k ~r> c_x} τ)]) as Hokd.
    { apply wf_ctxrR_regular1 in H1.
      eapply state_subst_implies_rty_subst_ok_dctx_all_v_to_c in H1; eauto.
      fast_set_solver. }
    listctx_set_simpl.
    destruct τ; invclear H1; try auto_ty_exfalso.
    + constructor; auto. intros.
      rewrite unfold_rty_obase in H1.
      apply state_subst_implies_rty_subst_rR_all_c_to_v in H1; auto.
      invclear H5; auto.
    + constructor; auto.
      { intros. apply H10. rewrite unfold_rty_ubase in H1.
        apply state_subst_implies_rty_subst_rR_all_c_to_v in H1; auto.
        invclear H6; auto. }
      mydestr. exists x0; split; eauto.
      rewrite unfold_rty_ubase. apply state_subst_implies_rty_subst_rR_all_v_to_c; auto.
      refinement_solver.
    + constructor; auto. intros.
      apply H8.
      apply state_subst_implies_rty_subst_rR_all_c_to_v in H1; auto.
      invclear H7; auto.
    + constructor; auto. intros.
      apply H8.
      apply state_subst_implies_rty_subst_rR_all_c_to_v in H1; auto.
      invclear H7; auto.
 - assert (ok_dctx (dom aset (<[a:=c_x]> st)) ((a0 :: Γ) ++ [(x, {k ~r> c_x} τ)])) as Hokd.
    { apply wf_ctxrR_regular1 in H1.
      eapply state_subst_implies_rty_subst_ok_dctx_all_v_to_c in H1; eauto.
      fast_set_solver. }
   invclear H1.
   + constructor; auto. intros. auto_under c_x0.
     setoid_rewrite insert_commute in H6; try fast_set_solver.
     setoid_rewrite insert_commute; try fast_set_solver.
     apply IHΓ; refinement_solver.
   + constructor; auto. mydestr. exists x1; split; eauto.
     intros. auto_under e_x. dsimp1.
     setoid_rewrite insert_commute in H2; try fast_set_solver.
     setoid_rewrite insert_commute; try fast_set_solver.
     apply IHΓ; refinement_solver.
   + constructor; auto. apply IHΓ; refinement_solver.
Qed.

Lemma state_subst_implies_rty_subst_wf_ctxrR_all_c_to_v
    : ∀ (a: atom) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) τ,
  a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
  closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> a} τ) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> c_x} τ)]) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> a} τ)]).
Proof.
  intros a. induction Γ; intros.
  - assert (ok_dctx (dom aset (<[a:=c_x]> st)) [(x, {k ~r> a} τ)]) as Hokd.
    { apply wf_ctxrR_regular1 in H1.
      eapply state_subst_implies_rty_subst_ok_dctx_all_c_to_v in H1; eauto.
      fast_set_solver. }
    listctx_set_simpl.
    destruct τ; invclear H1; try auto_ty_exfalso.
    + constructor; auto. intros.
      rewrite unfold_rty_obase in H1.
      apply state_subst_implies_rty_subst_rR_all_v_to_c in H1; auto.
      invclear H5; auto.
    + constructor; auto.
      { intros. apply H10. rewrite unfold_rty_ubase in H1.
        apply state_subst_implies_rty_subst_rR_all_v_to_c in H1; auto.
        invclear H6; auto. }
      mydestr. exists x0; split; eauto.
      rewrite unfold_rty_ubase. apply state_subst_implies_rty_subst_rR_all_c_to_v; auto.
      refinement_solver.
    + constructor; auto. intros.
      apply H8.
      apply state_subst_implies_rty_subst_rR_all_v_to_c in H1; auto.
      invclear H7; auto.
    + constructor; auto. intros.
      apply H8.
      apply state_subst_implies_rty_subst_rR_all_v_to_c in H1; auto.
      invclear H7; auto.
 - assert (ok_dctx (dom aset (<[a:=c_x]> st)) ((a0 :: Γ) ++ [(x, {k ~r> a} τ)])) as Hokd.
    { apply wf_ctxrR_regular1 in H1.
      eapply state_subst_implies_rty_subst_ok_dctx_all_c_to_v in H1; eauto.
      fast_set_solver. }
   invclear H1.
   + constructor; auto. intros. auto_under c_x0.
     setoid_rewrite insert_commute in H6; try fast_set_solver.
     setoid_rewrite insert_commute; try fast_set_solver.
     apply IHΓ; refinement_solver.
   + constructor; auto. mydestr. exists x1; split; eauto.
     intros. auto_under e_x. dsimp1.
     setoid_rewrite insert_commute in H2; try fast_set_solver.
     setoid_rewrite insert_commute; try fast_set_solver.
     apply IHΓ; refinement_solver.
   + constructor; auto. apply IHΓ; refinement_solver.
Qed.

Lemma state_subst_implies_rty_subst_wf_ctxrR_all_open_to_v
  : ∀ (a: atom) (v: value) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) τ,
    ((exists (n: constant), v = n) \/ (exists (y: atom), v = y)) ->
    a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> v} τ) ->
    wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> {a := c_x}v v} τ)]) ->
    wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> v} τ)]).
Proof.
  intros. destruct H; mydestr; subst; auto.
  destruct (decide (a = x0)); subst; auto.
  - simpl in H2. rewrite decide_True in H2; auto.
    eapply state_subst_implies_rty_subst_wf_ctxrR_all_c_to_v; auto.
  - simpl in H2. dec_solver2.
Qed.

Lemma state_subst_implies_rty_subst_wf_ctxrR_all_v_to_open
  : ∀ (a: atom) (v: value) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) τ,
    ((exists (n: constant), v = n) \/ (exists (y: atom), v = y)) ->
    a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset (<[a:=c_x]> st)) ({k ~r> {a := c_x}v v} τ) ->
    wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> v} τ)]) ->
    wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> {a := c_x}v v} τ)]).
Proof.
  intros. destruct H; mydestr; subst; auto.
  destruct (decide (a = x0)); subst; auto.
  - simpl in H1. rewrite decide_True in H1; auto.
    simpl. rewrite decide_True; auto.
    eapply state_subst_implies_rty_subst_wf_ctxrR_all_v_to_c; auto.
  - dec_solver2.
Qed.
