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
From CT Require Import InvDenotationProp1.
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

Global Hint Resolve mk_eq_constant_is_not_overbasety: core.
Global Hint Resolve mk_eq_var_is_not_overbasety: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Constructors ok_dctx: core.
Global Hint Resolve rR_implies_no_free: core.
Global Hint Resolve ctxrR_tlete_drop_halt_lhs: core.
Global Hint Resolve rR_implies_reduction_no_free: core.
Global Hint Resolve is_arr_implies_not_overbasety: core.
Global Hint Resolve under_not_overbasety: core.

Lemma inv_basety_implies_constant_or_var: forall Γ st b n d ϕ (v: value),
    (⅋{st}⟦[v:b|n|d|ϕ]⟧{Γ}) v -> ((exists (n: constant), v = n) \/ (exists (y: atom), v = y)).
Proof.
  intros. apply inv_ctxrR_regular in H; mydestr; eauto. invclear H.
  eapply has_basety_implies_constant_or_var; eauto.
Qed.

Lemma state_subst_implies_rty_subst_eq: forall (a: atom) (c_x: constant) Γ st τ x k b n d ϕ e,
    ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> a} [v:b|n|d|ϕ])]) ->
    ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> c_x} [v:b|n|d|ϕ])]) ->
    (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> c_x} [v:b|n|d|ϕ])] } e) <->
    (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> a} [v:b|n|d|ϕ])] } e).
Proof.
  induction Γ; split; intros; RD_simp2.
  - mydestr. simpl. constructor; auto.
    exists x0. split; auto. invclear H1; mydestr. constructor; auto. split; auto. refinement_solver.
  - mydestr. simpl. constructor; auto.
    exists x0. split; auto. invclear H1; mydestr. constructor; auto. split; auto. refinement_solver.
  - constructor; auto. inv_rd_simpl1. inv_rd_simpl1. intros. auto_under c_x0.
    assert (a0 <> a).
    { rewrite dom_insert_simp in H. apply ok_dctx_regular in H; mydestr. set_solver. }
    setoid_rewrite insert_commute; auto.
    eapply IHΓ; eauto.
    + repeat rewrite dom_insert_simp. invclear H; auto_ty_exfalso. rewrite dom_insert_simp in H15. ok_dctx_solver_slow.
    + repeat rewrite dom_insert_simp. invclear H7; auto_ty_exfalso. rewrite dom_insert_simp in H15. ok_dctx_solver_slow.
    + setoid_rewrite insert_commute; auto.
  - constructor; auto. inv_rd_simpl1. inv_rd_simpl1. intros. auto_under c_x0. mydestr.
    assert (a0 <> a).
    { rewrite dom_insert_simp in H. apply ok_dctx_regular in H; mydestr. set_solver. }
    exists x0. split; auto. intros. auto_under v_x. dsimp1.
    setoid_rewrite insert_commute; auto.
    eapply IHΓ; eauto.
    + repeat rewrite dom_insert_simp. invclear H; auto_ty_exfalso. ok_dctx_solver_slow.
    + repeat rewrite dom_insert_simp. invclear H7; auto_ty_exfalso. ok_dctx_solver_slow.
    + setoid_rewrite insert_commute; auto.
  - constructor; auto. inv_rd_simpl1. inv_rd_simpl1. intros. auto_under v_x.
    eapply IHΓ; eauto.
    + repeat rewrite dom_insert_simp. invclear H; auto_ty_exfalso. ok_dctx_solver_slow.
    + repeat rewrite dom_insert_simp. invclear H0; auto_ty_exfalso. ok_dctx_solver_slow.
  - constructor; auto. inv_rd_simpl1. inv_rd_simpl1. intros. auto_under c_x0.
    assert (a0 <> a).
    { rewrite dom_insert_simp in H. apply ok_dctx_regular in H; mydestr. set_solver. }
    setoid_rewrite insert_commute; auto.
    eapply IHΓ; eauto.
    + repeat rewrite dom_insert_simp. invclear H; auto_ty_exfalso. ok_dctx_solver_slow.
    + repeat rewrite dom_insert_simp. invclear H0; auto_ty_exfalso. ok_dctx_solver_slow.
    + setoid_rewrite insert_commute; auto.
  - constructor; auto. inv_rd_simpl1. inv_rd_simpl1. mydestr. exists x0. split; auto. intros.
    auto_under v_x. dsimp1.
    assert (a0 <> a).
    { apply ok_dctx_regular in H; mydestr. set_solver. }
    setoid_rewrite insert_commute; auto.
    eapply IHΓ; eauto.
    + repeat rewrite dom_insert_simp. invclear H; auto_ty_exfalso. ok_dctx_solver_slow.
    + repeat rewrite dom_insert_simp. invclear H0; auto_ty_exfalso. ok_dctx_solver_slow.
    + setoid_rewrite insert_commute; auto.
  - constructor; auto. inv_rd_simpl1. inv_rd_simpl1. intros.
    auto_under v_x.
    eapply IHΓ; eauto.
    + repeat rewrite dom_insert_simp. invclear H; auto_ty_exfalso. ok_dctx_solver_slow.
    + repeat rewrite dom_insert_simp. invclear H0; auto_ty_exfalso. ok_dctx_solver_slow.
Qed.

Lemma state_subst_implies_rty_subst_eq': forall (a: atom) (c_x: constant) Γ st τ x k b n d ϕ e,
    (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> a} [v:b|n|d|ϕ])]) /\
       (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> c_x} [v:b|n|d|ϕ])] } e)) <->
    (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> c_x} [v:b|n|d|ϕ])]) /\
       (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> a} [v:b|n|d|ϕ])] } e)).
Proof.
  split; intros; mydestr.
  - assert (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> c_x} [v:b|n|d|ϕ])])).
    apply inv_ctxrR_regular in H0; mydestr; auto.
    split; auto. rewrite <- state_subst_implies_rty_subst_eq; auto.
  - assert (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> a} [v:b|n|d|ϕ])])).
    apply inv_ctxrR_regular in H0; mydestr; auto.
    split; auto. rewrite state_subst_implies_rty_subst_eq; auto.
Qed.

Lemma state_subst_implies_rty_subst_eq2: forall (a v: atom) Γ st (c_x: constant) τ x k b n d ϕ e,
    (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])]) /\
        ⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> ({a := c_x}v v)} [v:b|n|d|ϕ])] } e) <->
    (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> ({a := c_x}v v)} [v:b|n|d|ϕ])]) /\
       ⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])] } e).
Proof.
  intros a v. destruct (decide (a = v)).
  - assert (forall c_x, ({a := c_x}v v) = c_x) as HJ by (simpl; intros; rewrite decide_True; auto).
    intros. rewrite HJ. subst. rewrite state_subst_implies_rty_subst_eq'; auto.
  - intros. rewrite subst_fresh_value; auto. fast_set_solver.
Qed.

Lemma state_subst_implies_rty_subst_eq2_forward
  : ∀ (a v : atom) (Γ : list (atom * rty)) (st : state) (c_x : constant) (τ : rty) (x : atom)
      (k : nat) (b : base_ty) (n : nat) (d : aset) (ϕ : refinement) (e : tm),
    ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> {a := c_x }v v} [v:b|n|d|ϕ])]) ->
    (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])] }) e ->
    (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> {a := c_x }v v} [v:b|n|d|ϕ])] }) e.
Proof.
  intros.
  assert (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> {a := c_x }v v} [v:b|n|d|ϕ])]) /\
         (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])] }) e). split; auto.
  rewrite <- state_subst_implies_rty_subst_eq2 in H1; mydestr; auto.
Qed.

Lemma state_subst_implies_rty_subst_eq2_backward
  : ∀ (a v : atom) (Γ : list (atom * rty)) (st : state) (c_x : constant) (τ : rty) (x : atom)
      (k : nat) (b : base_ty) (n : nat) (d : aset) (ϕ : refinement) (e : tm),
    ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])]) ->
    (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> {a := c_x }v v} [v:b|n|d|ϕ])] }) e ->
    (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])] }) e.
Proof.
  intros.
  assert (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])]) /\
         (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> {a := c_x }v v} [v:b|n|d|ϕ])]  }) e). split; auto.
  rewrite state_subst_implies_rty_subst_eq2 in H1; mydestr; auto.
Qed.

Lemma state_subst_implies_rty_subst_eq2_forward2
  : ∀ (a: atom) (Γ : list (atom * rty)) (st : state) (c_x : constant) (τ : rty) (x : atom)
      (k : nat) (b : base_ty) (n : nat) (d : aset) (ϕ : refinement) (e : tm),
    not_fv_in_refinement d ϕ -> bound_in_refinement (n `min` k) (refinement_open k c_x ϕ) ->
    (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> a} [v:b|n|d|ϕ])] }) e ->
    (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {k ~r> c_x} [v:b|n|d|ϕ])] }) e.
Proof.
  intros. apply state_subst_implies_rty_subst_eq2_forward in H1; biop_simpl; auto.
  apply inv_ctxrR_regular in H1; mydestr.
  apply state_subst_implies_rty_subst_eq2_forward_ok_dctx with (a:=a) (c_x:=c_x) in H2;  biop_simpl; eauto.
Qed.

Lemma state_subst_implies_rty_subst_eq2_forward_wf_ctxrR
    : ∀ (a v : atom) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) (b : base_ty) (n : nat) (d : aset) (ϕ : refinement),
  not_fv_in_refinement d ϕ -> a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
  bound_in_refinement (n `min` k) (refinement_open k c_x ϕ) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])]) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> {a := c_x }v v} [v:b|n|d|ϕ])]).
Proof.
  intros a v. induction Γ; intros.
  - listctx_set_simpl.
    assert (ok_dctx (dom aset (<[a:=c_x]> st)) ([] ++ [(x, {k ~r> v} [v:b|n|d|ϕ])])).
    { apply wf_ctxrR_regular1 in H2; auto. }
    constructor; auto.
    + eapply state_subst_implies_rty_subst_eq2_forward_ok_dctx in H3; eauto.
    + invclear H2; auto; try auto_ty_exfalso. intros. apply H12.
      assert ({0;b∅;<[a:=c_x]> st}⟦ {k ~r> {a := c_x }v v} [v:b|n|d|ϕ] ⟧ e_wf); auto.
      apply state_subst_implies_rty_subst_eq2_rR_backward in H4; auto.
      refinement_solver.
    + invclear H2; auto; try auto_ty_exfalso. mydestr. exists x0. split; eauto.
       assert ({0;b∅;<[a:=c_x]> st}⟦ {k ~r> v} [v:b|n|d|ϕ] ⟧ x0); auto.
       apply state_subst_implies_rty_subst_eq2_rR_forward in H5; auto.
       apply state_subst_implies_rty_subst_eq2_forward_closed_rty; auto.
       refinement_solver.
  - RD_simp2.
    + constructor; auto.
      { rewrite app_comm_cons.
        apply state_subst_implies_rty_subst_eq2_forward_ok_dctx; auto. }
      intros. setoid_rewrite insert_commute; try fast_set_solver.
      apply IHΓ; auto. setoid_rewrite dom_insert_simp; auto. set_solver.
      setoid_rewrite insert_commute; try fast_set_solver.
    + mydestr. constructor; auto.
      { rewrite app_comm_cons.
        apply state_subst_implies_rty_subst_eq2_forward_ok_dctx; auto. }
      exists x0. split; auto. intros. eapply H3 in H4; eauto.
      assert (exists (c: constant), v_x = c). dsimp1; eauto. mydestr; subst.
      setoid_rewrite insert_commute; try fast_set_solver.
      apply IHΓ; auto. setoid_rewrite dom_insert_simp; auto. set_solver.
      setoid_rewrite insert_commute; try fast_set_solver.
    + constructor; auto.
      { rewrite app_comm_cons.
        apply state_subst_implies_rty_subst_eq2_forward_ok_dctx; auto. }
      apply IHΓ; auto. set_solver.
Qed.

Lemma state_subst_implies_rty_subst_eq2_forwardc_wf_ctxrR
    : ∀ (a : atom) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) (b : base_ty) (n : nat) (d : aset) (ϕ : refinement),
  not_fv_in_refinement d ϕ -> a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
  bound_in_refinement (n `min` k) (refinement_open k c_x ϕ) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> a} [v:b|n|d|ϕ])]) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> c_x} [v:b|n|d|ϕ])]).
Proof.
  intros.
  apply state_subst_implies_rty_subst_eq2_forward_wf_ctxrR in H2; biop_simpl; auto.
Qed.

Lemma state_subst_implies_rty_subst_eq2_backward_wf_ctxrR
    : ∀ (a v : atom) (Γ : list (atom * rty)) st (c_x : constant) (x : atom)
      (k : nat) (b : base_ty) (n : nat) (d : aset) (ϕ : refinement),
  a ∉ (stale st ∪ stale Γ ∪ {[x]}) ->
  ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])]) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> {a := c_x }v v} [v:b|n|d|ϕ])]) ->
  wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])]).
Proof.
  intros a v. induction Γ; intros.
  - listctx_set_simpl.
    constructor; auto.
    + invclear H1; auto; try auto_ty_exfalso. intros. apply H10.
      assert ({0;b∅;<[a:=c_x]> st}⟦ {k ~r> {a := c_x }v v} [v:b|n|d|ϕ] ⟧ e_wf); auto.
      apply state_subst_implies_rty_subst_eq2_rR_forward in H1; auto.
      refinement_solver.
    + invclear H1; auto; try auto_ty_exfalso. mydestr. exists x0. split; eauto.
       assert ({0;b∅;<[a:=c_x]> st}⟦ {k ~r> {a := c_x }v v} [v:b|n|d|ϕ] ⟧ x0); auto.
       apply state_subst_implies_rty_subst_eq2_rR_backward in H3; auto.
       refinement_solver.
  - RD_simp2; invclear H0; try auto_ty_exfalso.
    + constructor; auto.
      intros. setoid_rewrite insert_commute; try fast_set_solver.
      apply IHΓ; auto. setoid_rewrite dom_insert_simp; auto. set_solver.
      setoid_rewrite insert_commute; try fast_set_solver. setoid_rewrite dom_insert_simp; auto.
      setoid_rewrite insert_commute; try fast_set_solver.
    + mydestr. constructor; auto.
      exists x0. split; auto. intros. eapply H1 in H2; eauto.
      assert (exists (c: constant), v_x = c). dsimp1; eauto. mydestr; subst.
      setoid_rewrite insert_commute; try fast_set_solver.
      apply IHΓ; auto. setoid_rewrite dom_insert_simp; auto. set_solver.
      setoid_rewrite insert_commute; try fast_set_solver. setoid_rewrite dom_insert_simp; auto.
      setoid_rewrite insert_commute; try fast_set_solver.
    + constructor; auto.
      apply IHΓ; auto. set_solver.
Qed.

Lemma mk_op_ret_wf_ctxrR
    : ∀ st op (a : atom) (v1 v2: value) (Γ : list (atom * rty)) (c_x : constant) (x: atom),
    ((exists (n: constant), v1 = n) \/ (exists (y: atom), v1 = y)) ->
    ((exists (n: constant), v2 = n) \/ (exists (y: atom), v2 = y)) ->
    a ∉ stale st ∪ stale Γ ∪ {[x]} ->
    (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))]) /\
       (wf_ctxrR (<[a:=c_x]> st)
          (Γ ++ [(x, {1 ~r> ({a := c_x }v v2)} (mk_op_ret op ^r^ ({a := c_x }v v1)))]))
    ) <-> (wf_ctxrR (<[a:=c_x]> st) (Γ ++ [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))])).
Proof.
  split; intros; mydestr; subst.
  - destruct H; destruct H0; mydestr; subst; auto.
    + destruct (decide (a = x0)); auto; subst; biop_simpl; auto.
      apply state_subst_implies_rty_subst_eq2_backward_wf_ctxrR; biop_simpl; auto.
    + destruct (decide (a = x1)); auto; subst; biop_simpl; auto.
      rewrite rty_open_commute_op; auto.
      rewrite rty_open_commute_op in H3; auto.
      rewrite rty_open_commute_op in H2; auto.
      apply state_subst_implies_rty_subst_eq2_backward_wf_ctxrR; biop_simpl; auto.
    + destruct (decide (a = x0)); auto; subst; auto.
      { biop_simpl.
        destruct (decide (x0 = x1)); auto; subst.
        - biop_simpl.
          assert (ok_dctx (dom aset (<[x1:=c_x]> st)) (Γ ++ [(x, {1 ~r> c_x} (mk_op_ret op ^r^ x1))])).
          { apply state_subst_implies_rty_subst_eq2_forward_ok_dctx with (a:=x1) (c_x :=c_x) in H2; eauto. biop_simpl; auto.
          unfold refinement_set_open. apply tletbiop_aux1; auto.
          assert ((2 `min` 0) `min` 1 = 0) by lia. setoid_rewrite H. clear H.
          apply tletbiop_aux2. }
          assert (wf_ctxrR (<[x1:=c_x]> st) (Γ ++ [(x, {1 ~r> c_x} (mk_op_ret op ^r^ x1))])).
          { rewrite rty_open_commute_op; auto.
            rewrite rty_open_commute_op in H3; auto.
            rewrite rty_open_commute_op in H; auto.
            apply state_subst_implies_rty_subst_eq2_backward_wf_ctxrR; biop_simpl; auto. }
          apply state_subst_implies_rty_subst_eq2_backward_wf_ctxrR; biop_simpl; auto.
        - apply state_subst_implies_rty_subst_eq2_backward_wf_ctxrR; biop_simpl; auto.
      }
      { rewrite rty_open_commute_op in H2; auto.
        rewrite rty_open_commute_op in H3; auto.
        rewrite rty_open_commute_op; auto.
        apply state_subst_implies_rty_subst_eq2_backward_wf_ctxrR; biop_simpl; auto.
 }
 - split. apply wf_ctxrR_regular1 in H2; mydestr; auto.
    destruct H; destruct H0; mydestr; subst; auto.
    + destruct (decide (a = x0)); auto; subst; biop_simpl; auto.
      apply state_subst_implies_rty_subst_eq2_forwardc_wf_ctxrR; biop_simpl; auto.
      pose (not_fv_in_refinement_aux op x1 0) as Hn; apply Hn; try lia; eauto.
      apply tletbiop_aux6; eauto.
    + destruct (decide (a = x1)); auto; subst; biop_simpl; auto.
      rewrite rty_open_commute_op; auto.
      rewrite rty_open_commute_op in H2; auto.
      apply state_subst_implies_rty_subst_eq2_forwardc_wf_ctxrR; biop_simpl; auto.
      pose (not_fv_in_refinement_aux op x0 1) as Hn; apply Hn; try lia; eauto.
      apply tletbiop_aux7; eauto.
    + destruct (decide (a = x0)); auto; subst; auto; biop_simpl.
      { destruct (decide (x0 = x1)); auto; subst; biop_simpl.
        - assert (wf_ctxrR (<[x1:=c_x]> st) (Γ ++ [(x, {1 ~r> x1} (mk_op_ret op ^r^ c_x))] )).
          rewrite rty_open_commute_op; auto.
          rewrite rty_open_commute_op in H2; auto.
          apply state_subst_implies_rty_subst_eq2_forwardc_wf_ctxrR; biop_simpl; auto.
          pose (not_fv_in_refinement_aux op x1 1) as Hn; simpl; rewrite tletbiop_aux8; apply Hn; try lia; eauto.
          simpl. apply tletbiop_aux7; eauto.
          apply state_subst_implies_rty_subst_eq2_forwardc_wf_ctxrR; biop_simpl; auto.
          pose (not_fv_in_refinement_aux op c_x 0) as Hn; simpl; try rewrite tletbiop_aux8; apply Hn; try lia; eauto.
          simpl. apply tletbiop_aux6; eauto.
        - apply state_subst_implies_rty_subst_eq2_forwardc_wf_ctxrR; biop_simpl; auto.
          pose (not_fv_in_refinement_aux op x1 0) as Hn; simpl; try rewrite tletbiop_aux8; apply Hn; try lia; eauto.
          simpl. apply tletbiop_aux6; eauto.
      }
      { destruct (decide (a = x1)); auto; subst; biop_simpl; auto.
        rewrite rty_open_commute_op; auto.
        rewrite rty_open_commute_op in H2; auto.
        apply state_subst_implies_rty_subst_eq2_forwardc_wf_ctxrR; biop_simpl; auto.
        pose (not_fv_in_refinement_aux op x0 1) as Hn; simpl; try rewrite tletbiop_aux8; apply Hn; try lia; eauto.
        simpl. apply tletbiop_aux7; eauto.
      }
Qed.

Lemma mk_op_ret_ok_dctx
    : ∀ st op (a : atom) (v1 v2: value) (Γ : list (atom * rty)) (c_x : constant) (x : atom) e τ,
    ((exists (n: constant), v1 = n) \/ (exists (y: atom), v1 = y)) ->
    ((exists (n: constant), v2 = n) \/ (exists (y: atom), v2 = y)) ->
    (ok_dctx (dom aset (<[a:=c_x]> st)) (Γ ++ [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))]) /\
    (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {1 ~r> ({a := c_x }v v2)} (mk_op_ret op ^r^ ({a := c_x }v v1)))] } e)) <->
       (⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++ [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))] }) e.
Proof.
  split; intros; mydestr; subst.
  - destruct H; destruct H0; mydestr; subst; auto.
    + destruct (decide (a = x0)); auto; subst; biop_simpl; auto.
      apply state_subst_implies_rty_subst_eq2_backward; biop_simpl; auto.
    + destruct (decide (a = x1)); auto; subst; biop_simpl; auto.
      rewrite rty_open_commute_op; auto.
      rewrite rty_open_commute_op in H1; auto.
      rewrite rty_open_commute_op in H2; auto.
      apply state_subst_implies_rty_subst_eq2_backward; biop_simpl; auto.
    + destruct (decide (a = x0)); auto; subst; auto.
      { biop_simpl.
        destruct (decide (x0 = x1)); auto; subst.
        - biop_simpl.
          assert (ok_dctx (dom aset (<[x1:=c_x]> st)) (Γ ++ [(x, {1 ~r> c_x} (mk_op_ret op ^r^ x1))])).
          { apply state_subst_implies_rty_subst_eq2_forward_ok_dctx with (a:=x1) (c_x :=c_x) in H1; eauto. biop_simpl; auto.
          unfold refinement_set_open. apply tletbiop_aux1; auto.
          assert ((2 `min` 0) `min` 1 = 0) by lia. setoid_rewrite H. clear H.
          apply tletbiop_aux2. }
          assert ((⅋{<[x1:=c_x]> st}⟦τ⟧{Γ ++ [(x, {1 ~r> c_x} (mk_op_ret op ^r^ x1))] }) e).
          { rewrite rty_open_commute_op; auto.
            rewrite rty_open_commute_op in H; auto.
            rewrite rty_open_commute_op in H2; auto.
            apply state_subst_implies_rty_subst_eq2_backward; biop_simpl; auto. }
          apply state_subst_implies_rty_subst_eq2_backward; biop_simpl; auto.
        - apply state_subst_implies_rty_subst_eq2_backward; biop_simpl; auto.
      }
      { rewrite rty_open_commute_op in H1; auto.
        rewrite rty_open_commute_op in H2; auto.
        rewrite rty_open_commute_op; auto.
        apply state_subst_implies_rty_subst_eq2_backward; biop_simpl; auto. }
  - split. try (apply inv_ctxrR_regular in H1; mydestr; auto).
    destruct H; destruct H0; mydestr; subst; auto.
    + destruct (decide (a = x0)); auto; subst; biop_simpl; auto.
      apply state_subst_implies_rty_subst_eq2_forward2; biop_simpl; auto.
      pose (not_fv_in_refinement_aux op x1 0) as Hn; apply Hn; try lia; eauto.
      apply tletbiop_aux6; eauto.
    + destruct (decide (a = x1)); auto; subst; biop_simpl; auto.
      rewrite rty_open_commute_op; auto.
      rewrite rty_open_commute_op in H1; auto.
      apply state_subst_implies_rty_subst_eq2_forward2; biop_simpl; auto.
      pose (not_fv_in_refinement_aux op x0 1) as Hn; apply Hn; try lia; eauto.
      apply tletbiop_aux7; eauto.
    + destruct (decide (a = x0)); auto; subst; auto; biop_simpl.
      { destruct (decide (x0 = x1)); auto; subst; biop_simpl.
        - assert ((⅋{<[x1:=c_x]> st}⟦τ⟧{Γ ++ [(x, {1 ~r> x1} (mk_op_ret op ^r^ c_x))] }) e).
          rewrite rty_open_commute_op; auto.
          rewrite rty_open_commute_op in H1; auto.
          apply state_subst_implies_rty_subst_eq2_forward2; biop_simpl; auto.
          pose (not_fv_in_refinement_aux op x1 1) as Hn; simpl; rewrite tletbiop_aux8; apply Hn; try lia; eauto.
          simpl. apply tletbiop_aux7; eauto.
          apply state_subst_implies_rty_subst_eq2_forward2; biop_simpl; auto.
          pose (not_fv_in_refinement_aux op c_x 0) as Hn; simpl; try rewrite tletbiop_aux8; apply Hn; try lia; eauto.
          simpl. apply tletbiop_aux6; eauto.
        - apply state_subst_implies_rty_subst_eq2_forward2; biop_simpl; auto.
          pose (not_fv_in_refinement_aux op x1 0) as Hn; simpl; try rewrite tletbiop_aux8; apply Hn; try lia; eauto.
          simpl. apply tletbiop_aux6; eauto.
      }
      { destruct (decide (a = x1)); auto; subst; biop_simpl; auto.
        rewrite rty_open_commute_op; auto.
        rewrite rty_open_commute_op in H1; auto.
        apply state_subst_implies_rty_subst_eq2_forward2; biop_simpl; auto.
        pose (not_fv_in_refinement_aux op x0 1) as Hn; simpl; try rewrite tletbiop_aux8; apply Hn; try lia; eauto.
        simpl. apply tletbiop_aux7; eauto.
      }
Qed.

Lemma inv_rRctx_tletbiop: forall Γ st (τ: rty) x op n1 d1 ϕ1 n2 d2 ϕ2 (v1 v2: value) e,
    x ∉ fv_tm e -> x ∉ rty_fv τ -> not_overbasety τ ->
    wf_ctxrR st (Γ ++ [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))]) ->
    (⅋{st}⟦[v:fst_ty_of_op op|n1|d1|ϕ1]⟧{Γ}) v1 ->
    (⅋{st}⟦[v:snd_ty_of_op op|n2|d2|ϕ2]⟧{Γ}) v2 ->
    (⅋{st}⟦τ⟧{Γ ++ [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))] }) (e ^t^ x) ->
    ⅋{st}⟦τ⟧{Γ ++ [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))] } (tletbiop op v1 v2 e).
Proof.
  induction Γ; intros; RD_simp2.
  - mydestr. inv_rd_simpl1. constructor; auto.
    + denotation_simp. assert ([] ⊢t tletbiop op v1 v2 e ⋮t ⌊τ⌋). eapply tletbiop_typable; refinement_solver.
      basic_typing_solver.
    + assert ((exists (m1: nat), v1 = m1)) by (eapply fst_ty_of_op_implies_nat; eauto). mydestr; subst. rename x2 into v1.
      assert ((exists (m2: nat), v2 = m2)) by (eapply snd_ty_of_op_implies_nat; eauto). mydestr; subst. rename x2 into v2.
      exists (eval_op_under_bound_tm op v1 v2). split. apply rR_eval_op_under_bound_tm.
      intros. assert (x1 ↪* v_x) as Hz by (eapply rR_eval_op_under_bound_tm_min; eauto).
      auto_under v_x. RD_simp2. simpl.
      rewrite subst_fresh_tm; auto. rewrite open_subst_same_tm in H10; auto.
      eapply termR_perserve_rR; refinement_solver.
      eapply letapp_eval_op_under_bound_tm_termR; eauto; refinement_solver.
  - constructor; auto. denotation_simp. apply tletbiop_typable_ctx_dummy_cons; auto.
    intros. auto_under c_x. invclear H11; auto_ty_exfalso.
    assert ((exists (n: constant), v1 = n) \/ (exists (y: atom), v1 = y)).
    { invclear H20. eapply has_basety_implies_constant_or_var; eauto. }
    assert ((exists (n: constant), v2 = n) \/ (exists (y: atom), v2 = y)).
    { invclear H23. eapply has_basety_implies_constant_or_var; eauto. }
    rewrite <- mk_op_ret_ok_dctx; auto. split; auto. rewrite dom_insert_simp; auto.
    assert (a <> x) by (rewrite ctxdom_app_union in H16; inv_rd_simpl1).
    eapply IHΓ; eauto; fold value_subst; fold tm_subst.
    + pose (fv_of_subst_tm a c_x e). set_solver.
    + assert (wf_ctxrR (<[a:=c_x]> st)
                (Γ ++ [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))])); auto.
      rewrite <- mk_op_ret_wf_ctxrR in H10; mydestr; auto. listctx_set_solver.
    + assert ((⅋{<[a:=c_x]> st}⟦τ⟧{Γ ++
                       [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))] }) ({a := c_x }t (e ^t^ x))
           ); auto.
      rewrite subst_open_tm in H10; auto.
      assert ({a := c_x}v x = x). { simpl. dec_solver2. }
      rewrite H11 in H10.
      rewrite <- mk_op_ret_ok_dctx in H10; mydestr; auto.
  - constructor; auto. denotation_simp. apply tletbiop_typable_ctx_dummy_cons; auto.
    mydestr. auto_meet_exists Hmeet. auto_meet_reduce. auto_under v_x.
    assert ((exists (n: constant), v1 = n) \/ (exists (y: atom), v1 = y)).
    { invclear H20. eapply has_basety_implies_constant_or_var; eauto. }
    assert ((exists (n: constant), v2 = n) \/ (exists (y: atom), v2 = y)).
    { invclear H23. eapply has_basety_implies_constant_or_var; eauto. }
    assert (exists (c: constant), v_x = c). dsimp1; eauto. mydestr; subst.
    assert (({a↦x4}) st = <[a:=x4]> st) as Htz; auto. rewrite Htz.
    rewrite <- mk_op_ret_ok_dctx; auto. split; auto.
    { apply inv_ctxrR_regular in H12; mydestr; auto. }
    assert (a <> x). { apply ok_dctx_regular in H11; mydestr. basic_typing_solver. }
    eapply IHΓ; eauto; fold value_subst; fold tm_subst.
    + rewrite fv_of_subst_tm_closed; refinement_solver.
    + eapply H3 in H2; eauto.
      assert (wf_ctxrR (<[a:=x4]> st)
                (Γ ++ [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))])); auto.
      rewrite <- mk_op_ret_wf_ctxrR in H28; mydestr; auto.
      apply ok_dctx_regular in H11; mydestr. simpl in H29. listctx_set_simpl.
      set_solver.
    + assert ((⅋{<[a:=x4]> st}⟦τ⟧{Γ ++
                       [(x, {1 ~r> v2} (mk_op_ret op ^r^ v1))] }) ({a := x4 }t (e ^t^ x))
           ); auto.
      rewrite subst_open_tm in H28; auto.
      assert ({a := x4}v x = x). { simpl. dec_solver2. }
      rewrite H29 in H28.
      rewrite <- mk_op_ret_ok_dctx in H28; mydestr; auto.
  - constructor; auto. denotation_simp. apply tletbiop_typable_ctx_dummy_cons; auto.
    intros. auto_under v_x.
    assert ((exists (n: constant), v1 = n) \/ (exists (y: atom), v1 = y)).
    { invclear H23. eapply has_basety_implies_constant_or_var; eauto. }
    assert ((exists (n: constant), v2 = n) \/ (exists (y: atom), v2 = y)).
    { invclear H19. eapply has_basety_implies_constant_or_var; eauto. }
    assert ({a := v_x }t tletbiop op v1 v2 e =
           tletbiop op ({a := v_x }v v1) ({a := v_x }v v2) ({a := v_x }t e)) as Htz; auto.
    rewrite Htz.
    assert ({a := v_x }v v1 = v1).
    { destruct H4; mydestr; subst; auto. simpl. dec_solver2; subst.
      invclear H23. invclear H22. simpl in H26. rewrite decide_True in H26. invclear H26.
      apply letebiop_aux9 with (op:=op) in H6. exfalso. apply H6; auto. reflexivity.
    }
    assert ({a := v_x }v v2 = v2).
    { destruct H5; mydestr; subst; auto. simpl. dec_solver2; subst.
      invclear H19. invclear H26. simpl in H27. rewrite decide_True in H27. invclear H27.
      apply letebiop_aux9 with (op:=op) in H6. exfalso. apply H6; auto. reflexivity.
    }
    rewrite H17. rewrite H22.
    assert ({a := v_x }t v1 = v1) by (simpl; rewrite H17; auto).
    assert ({a := v_x }t v2 = v2) by (simpl; rewrite H22; auto).
    rewrite H26 in H24.
    rewrite H27 in H20.
    eapply IHΓ; eauto; fold tm_subst.
    + rewrite fv_of_subst_tm_closed. denotation_simp. apply rR_implies_no_free_value in H2. auto.
    + rewrite <- subst_open_var_tm; auto. denotation_simp. basic_typing_solver. refinement_solver.
Qed.

