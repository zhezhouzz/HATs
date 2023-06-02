From stdpp Require Import mapset.
From stdpp Require Import natmap.
From stdpp Require Import fin_map_dom.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.
From CT Require Import RefinementType.
From CT Require Import RefinementTypeTac.
From CT Require Import RefinementTypeDenotationProp.
From CT Require Import CtxDenotation.
From CT Require Import TermOrdering.
From CT Require Import InvDenotationProp4.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.

Import Atom.
Import CoreLang.
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
Import CtxDenotation.
Import TermOrdering.
Import InvDenotation.
Import InvDenotationProp1.
Import InvDenotationProp2.
Import InvDenotationProp3.
Import InvDenotationProp4.

Lemma ctxrR_empty_iff_rR: forall st τ e, ({st}⟦τ⟧{ [] }) e <-> {st}⟦τ⟧ e.
Proof.
  split; intros; auto.
  - invclear H; auto.
  - constructor; auto.
Qed.

Lemma not_ctxrR_empty_iff_not_rR: forall st τ e, ~ ({st}⟦τ⟧{ [] }) e <-> ~ {st}⟦τ⟧ e.
Proof.
  split; intros; auto.
  - intros HF. apply H. constructor; auto.
  - intros HF. apply H. invclear HF; auto.
Qed.

Ltac RD_simp :=
  repeat (match goal with
          | [H: ({_}⟦ _ ⟧{ [] }) _ |- _ ] => invclear H
          | [|- ({_}⟦ _ ⟧{ [] }) _ ] => constructor
          | [H: ({_}⟦_⟧{ (_, {v:_|_|_|_}) :: _ }) _ |- _ ] => invclear H; try auto_ty_exfalso
          | [H: ({0;b∅;_}⟦{v:_|_|_|_}⟧) (tvalue ?u) |- _ ] =>
              match u with
              | vconst _ => idtac
              | _ => destruct (over_inhabitant_only_constant _ _ _ _ _ _ H); subst
              end
          | [H: ¬ ({_}⟦ _ ⟧{ [] }) _ |- _ ] => rewrite not_ctxrR_empty_iff_not_rR in H
          | [ |- ¬ ({_}⟦ _ ⟧{ [] }) _ ] => rewrite not_ctxrR_empty_iff_not_rR
          | [H: ({_}⟦?τ⟧{_}) _  |- closed_rty _ _ ?τ] => apply ctxrR_regular in H; mydestr
          | [H: ({_}⟦_⟧{?Γ}) _  |- ok_dctx _ ?Γ] => apply ctxrR_regular in H; mydestr; my_simplify_map_eq
          | [H: ({_}⟦?τ⟧{ _ }) _ |- closed_rty _ _ ?τ] =>
       apply ctxrR_regular in H; mydestr
          end; eauto).

Lemma inv_ctxrR_implies_ctxrR: forall Γ st τ e,
    not_overbasety τ -> ⅋{st}⟦τ⟧{Γ} e -> {st}⟦τ⟧{Γ} e.
Proof.
  induction Γ; intros. RD_simp2. RD_simp.
  RD_simp2.
  - constructor; auto.
  - constructor; auto. mydestr. auto_meet_exists Hmeet. auto_under v_x. dsimp1.
    apply IHΓ; auto.
    eapply termR_perserve_inv_ctxrR; eauto. refinement_solver.
    apply termR_trans_better with (tlete x0 (a \t\ e)).
    + apply termR_let_one_step_from_basic_type'. basic_typing_solver.
      refinement_solver. eapply let_store_typable; eauto. refinement_solver.
      rewrite basic_has_type_swap2_tm; auto.
    + eapply termR_elete_lhs with (x:=a) (Tx:=b); eauto.
      apply close_rm_fv_tm.
      apply termR_weakening. basic_typing_solver.
      apply termR_value_tm; auto.
      rewrite open_close_var_tm; basic_typing_solver.
      rewrite basic_has_type_swap2_tm; auto.
  - constructor; auto. auto_meet_exists Hmeet. reduction_simpl0. auto_under v_x.
    apply IHΓ; auto.
    erewrite state_insert_closed_value_arr; eauto; refinement_solver.
    eapply termR_perserve_inv_ctxrR; eauto. refinement_solver.
    apply termR_let_one_step_from_basic_type'. basic_typing_solver.
    refinement_solver. eapply let_store_typable; eauto. refinement_solver.
    rewrite basic_has_type_swap2_tm; auto.
Qed.

Lemma ctxrR2_implies_inv_ctxrR: forall Γ st τ1 τ2,
    ctxrR2 st Γ τ1 τ2 -> (forall e, ⅋{st}⟦ τ1 ⟧{ Γ } e -> ⅋{st}⟦ τ2 ⟧{ Γ } e).
Proof.
  induction Γ; intros. invclear H. RD_simp2. mydestr.
  invclear H.
  - RD_simp2. constructor; auto. rewrite <- H10; auto. intros. auto_under c_x.
    eapply IHΓ; eauto.
  - RD_simp2. constructor; auto. rewrite <- H10; auto. mydestr.
    auto_meet_exists Hmeet. auto_meet_reduce.
  - RD_simp2. constructor; auto. rewrite <- H11; auto. mydestr.
    assert ({st}⟦τ1⟧⊆⟦τ2⟧{Γ}).
    { assert (∃ v : value, ({0;b∅;st}⟦r⟧) v ∧ x ↪* v) by (apply rR_arr_halt; auto).
      mydestr. eapply H0 in H1; eauto.
      erewrite state_insert_closed_value_arr in H1; eauto. refinement_solver.
      apply multistep_refl. op_solver1. }
    intros. auto_under v_x. eapply IHΓ; eauto.
Qed.

Lemma rR_push_to_subst: forall (st: state) (x: atom) c_x τ e,
    x ∉ rty_fv τ ->
    closed_rty 0 ({[x]} ∪ dom aset st) (τ ^r^ x) ->
    {1;<b[↦c_x]> b∅;st}⟦τ⟧ e -> {0;b∅;<[x:=c_x]> st}⟦τ ^r^ x⟧ e.
Proof.
  intros.
  apply rR_open_trans_empty' in H1.
  rewrite <- rR_shadow_update_st_c with (a := x) (c := c_x) in H1.
  apply state_subst_implies_rty_subst_rR_all_c_to_v; auto.
  closed_rty_solver.
  refinement_solver. rewrite rty_fv_open_c_eq. auto.
Qed.

Lemma closed_rty_open_1: forall τ (L: aset) (c_x:constant),
    closed_rty 1 L τ -> closed_rty 0 L (τ ^r^ c_x).
Proof.
  induction τ; intros.
  - invclear H. constructor; auto.
  - invclear H. constructor; auto.
  - auto_dclosed_rty.
    assert (closed_rty 0 L ({v:B|n|d|ϕ} ^r^ c_x)). invclear H; constructor; auto.
    simpl. simpl in H2. auto_dclosed_rty.
  - simpl. auto_dclosed_rty.
Qed.

Lemma rR_push_to_subst': forall (st: state) (x: atom) c_x τ e,
    x ∉ rty_fv τ ->
    closed_rty 1 (dom aset st) (τ) ->
    {0;b∅;<[x:=c_x]> st}⟦τ ^r^ x⟧ e ->
    {1;<b[↦c_x]> b∅;st}⟦τ⟧ e.
Proof.
  intros.
  apply state_subst_implies_rty_subst_rR_all_v_to_c in H1; auto.
  apply rR_open_trans_empty; auto.
  rewrite rR_shadow_update_st_c with (a := x) (c := c_x) in H1; auto.
  rewrite rty_fv_open_c_eq. auto.
  apply closed_rty_open_1 with (c_x:=c_x)in H0. refinement_solver.
Qed.


Lemma inv_ctxrR2_oarr_rR: forall x st b n d ϕ1 ϕ2 τ1 τ2,
    x ∉ stale τ2 ∪ stale τ1 ∪ stale d ->
    closed_rty 0 (dom _ st) (-:{v: b | n | d | ϕ1}⤑ τ1) ->
    closed_rty 0 (dom _ st) (-:{v: b | n | d | ϕ2}⤑ τ2) ->
    {st}⟦{v:b|n|d|ϕ2}⟧⊆⟦{v:b|n|d|ϕ1}⟧{[] } ->
    {st}⟦τ1 ^r^ x⟧⊆⟦τ2 ^r^ x⟧{[(x, {v:b|n|d|ϕ2})] } ->
    {st}⟦-:{v: b | n | d | ϕ1}⤑ τ1⟧⊆⟦-:{v: b | n | d | ϕ2}⤑ τ2⟧{[] }.
Proof.
  intros. invclear H2. invclear H3; try auto_ty_exfalso.
  constructor; auto.
  { inv_rd_simpl0. rewrite H19; auto. }
  intros. simpl in H2; mydestr.
  constructor; auto.
  { inv_rd_simpl0. rewrite <- H19; auto. }
  constructor; auto. exists x0. split; auto. intros.
  assert (({0;b∅;st}⟦{v:b|n|d|ϕ2}⟧) c_x) as Hc_x2.
  { constructor; auto. constructor; auto. exists c_x; do 2 (split; eauto). }
  specialize (H7 _ Hc_x2) as Hc_x1.
  simpl in Hc_x1; mydestr; subst. invclear H21. rename x1 into c_x.
  apply H9 in H14; auto.
  specialize (H20 _ Hc_x2). invclear H20.
  apply rR_push_to_subst with (x:=x) in H14; try fast_set_solver; try closed_rty_solver.
  apply H24 in H14.
  eapply rR_push_to_subst'; eauto. fast_set_solver. auto_dclosed_rty.
Qed.

Lemma inv_ctxrR2_arrarr_rR: forall x st τ11 τ12 τ21 τ22,
    x ∉ stale τ11 ∪ stale τ12 ∪ stale τ21 ∪ stale τ22 ->
    closed_rty 0 (dom _ st) (τ11 ⤑ τ12) ->
    closed_rty 0 (dom _ st) (τ21 ⤑ τ22) ->
    {st}⟦τ21⟧⊆⟦τ11⟧{ [] } ->
    {st}⟦τ12⟧⊆⟦τ22⟧{[] } ->
    is_arr τ21 -> is_arr τ11 ->
    {st}⟦τ11 ⤑ τ12⟧⊆⟦τ21 ⤑ τ22⟧{ [] }.
Proof.
  intros. invclear H2. invclear H3; try auto_ty_exfalso.
  constructor; auto.
  { inv_rd_simpl0. rewrite H8; rewrite H11; auto. }
  intros. simpl in H3; mydestr.
  constructor; auto.
  { inv_rd_simpl0. rewrite H8; rewrite <- H11; auto. }
  constructor; auto. exists x0. split; auto.
Qed.


Lemma ctxrR2_implies_erase_eq: forall Γ st τ1 τ2,
  {st}⟦ τ1 ⟧⊆⟦ τ2 ⟧{Γ} -> ⌊ τ1 ⌋ = ⌊ τ2 ⌋.
Proof.
  intros. induction H; auto.
Qed.

Lemma ctxrR2_implies_closed_rty: forall Γ st τ1 τ2,
  {st}⟦ τ1 ⟧⊆⟦ τ2 ⟧{Γ} ->
  closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) τ1 /\ closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) τ2.
Proof.
  intros. induction H; split; auto; denotation_simp; try closed_rty_solver.
Qed.

Lemma ctxrR2_regular: forall Γ st τ1 τ2,
  {st}⟦ τ1 ⟧⊆⟦ τ2 ⟧{Γ} ->
  ⌊ τ1 ⌋ = ⌊ τ2 ⌋ /\ closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) τ1 /\ closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom aset st) τ2.
Proof.
  intros. split.
  eapply ctxrR2_implies_erase_eq; eauto.
  eapply ctxrR2_implies_closed_rty; eauto.
Qed.

Ltac closed_rty_solver2 :=
  match goal with
  | [H: closed_rty ?m ?L [v:?b|?n|?d|?ϕ] |- closed_rty ?m ?L {v:?b|?n|?d|?ϕ} ] =>
      rewrite closed_rty_under_iff_over; auto
  | [H: closed_rty ?m ?L {v:?b|?n|?d|?ϕ} |- closed_rty ?m ?L [v:?b|?n|?d|?ϕ] ] =>
      rewrite <- closed_rty_under_iff_over; auto
  end.

Lemma rR_implies_overbase_simpl: forall st b n d ϕ1 ϕ2,
    closed_rty 0 (dom aset st) {v:b|n|d|ϕ2} ->
    closed_rty 0 (dom aset st) {v:b|n|d|ϕ1} ->
    (∀ e : tm, ({0;b∅;st}⟦{v:b|n|d|ϕ1}⟧) e → ({0;b∅;st}⟦{v:b|n|d|ϕ2}⟧) e) <->
      (forall (c: constant), [] ⊢t c ⋮t b -> ϕ1 b∅ st c -> ϕ2 b∅ st c).
Proof.
  split; intros; mydestr.
  - intros. assert (({0;b∅;st}⟦{v:b|n|d|ϕ1}⟧) c). constructor; auto. constructor; auto.
    exists c. split; auto. basic_typing_solver.
    apply H1 in H4. invclear H4; mydestr; subst. invclear H8; auto.
  - simpl in H2; mydestr. invclear H6. constructor; auto. constructor; auto.
    exists x. split; auto.
Qed.

Definition not_eq_c (c: constant): tm :=
  match c with
  | cbool true => false
  | cbool false => true
  | cnat n =>
    tletbiop op_rannat (cnat 0) (cnat 0)
            (tletbiop op_eq n (vbvar 0)
               (tmatchb (vbvar 0) terr (vbvar 1)))
  end.

Lemma not_eq_c_typable: forall c, [] ⊢t not_eq_c c ⋮t ty_of_const c.
Proof.
  intros. destruct c; auto.
  - simpl. destruct b; eauto; constructor; constructor; auto.
  - simpl.
    econstructor; eauto. instantiate (1:=∅). intros. simpl.
    econstructor; eauto. repeat constructor; listctx_set_solver. repeat constructor; try listctx_set_solver. simpl. dec_solver1.
    instantiate (1:= {[x]}). intros. simpl.
    econstructor; eauto; try basic_typing_vfavr_solver.
    constructor; auto. listctx_set_solver.
    constructor; auto. basic_typing_vfavr_solver.
Qed.

Global Hint Resolve not_eq_c_typable: core.

Lemma not_eq_c_reduce_to_not_c: forall (c c': constant),
    ty_of_const c = ty_of_const c' ->
    c ≠ c' -> not_eq_c c ↪* c'.
Proof.
  intros. destruct c; destruct c'; invclear H.
  - simpl. destruct b; destruct b0; auto; auto_exfalso.
  - assert ([] ⊢t not_eq_c n ⋮t ty_of_const n) as HT by auto.
    assert (lc (not_eq_c n)) as Hlc by basic_typing_solver.
    simpl. simpl in Hlc. rewrite letbiop_lc_body in Hlc; mydestr.
    rewrite letbiop_step_spec. exists 0,0, n0. repeat (split; auto).
    simpl.
    rewrite letbiop_step_spec. exists n,n0,(n =? n0). repeat (split; auto).
    { unfold body. exists ∅. intros. simpl. lc_solver. }
    simpl. assert (n =? n0 = false). rewrite Nat.eqb_neq; auto. rewrite H3.
    eapply multistep_R. constructor; auto.
Qed.

Lemma not_eq_c_not_reduce_to_c: forall (c: constant), ~ not_eq_c c ↪* c.
Proof.
  intros. intro HF. destruct c; simpl in HF.
  - destruct b; invclear HF; invclear H.
  - rewrite letbiop_step_spec in HF; mydestr; subst.
    simpl in H3.
    rewrite letbiop_step_spec in H3; mydestr; subst.
    invclear H3. invclear H4. simpl in H7.
    invclear H7. invclear H3; try auto_reduction_exfalso.
    invclear H6. reduction_simpl0. invclear H3. rewrite Nat.eqb_neq in H8. neg_apply H8.
Qed.

Lemma rR_implies_underbase_simpl: forall st b n d ϕ1 ϕ2,
    closed_rty 0 (dom aset st) [v:b|n|d|ϕ2] ->
    closed_rty 0 (dom aset st) [v:b|n|d|ϕ1] ->
    (∀ e : tm, ({0;b∅;st}⟦[v:b|n|d|ϕ1]⟧) e → ({0;b∅;st}⟦[v:b|n|d|ϕ2]⟧) e) <->
      (forall (c: constant), [] ⊢t c ⋮t b -> ϕ2 b∅ st c -> ϕ1 b∅ st c).
Proof.
  split; intros; mydestr.
  - pbc. assert ({0;b∅;st}⟦[v:b|n|d|ϕ1]⟧ (not_eq_c c)).
    { constructor; auto. denotation_simp. constructor; auto. intros.
      apply not_eq_c_reduce_to_not_c. denotation_simp. neg_apply H4; subst; auto. }
    apply H1 in H5. simpl in H5; mydestr. apply H7 in H3; auto; basic_typing_solver.
    apply not_eq_c_not_reduce_to_c in H3. invclear H3.
  - simpl in H2; mydestr. constructor; auto.
Qed.

Lemma rR_implies_under_iff_over: forall st b n d ϕ1 ϕ2,
    closed_rty 0 (dom aset st) {v:b|n|d|ϕ1} ->
    closed_rty 0 (dom aset st) {v:b|n|d|ϕ2} ->
    (∀ e : tm, ({0;b∅;st}⟦[v:b|n|d|ϕ2]⟧) e → ({0;b∅;st}⟦[v:b|n|d|ϕ1]⟧) e) <->
      (∀ e : tm, ({0;b∅;st}⟦{v:b|n|d|ϕ1}⟧) e → ({0;b∅;st}⟦{v:b|n|d|ϕ2}⟧) e).
Proof.
  split; intros.
  - invclear H2; mydestr; subst. constructor; auto. constructor; auto.
    exists x. split; auto. split; auto.
    rewrite rR_implies_underbase_simpl in H1; eauto; closed_rty_solver2.
  - invclear H2; mydestr; subst. constructor; auto. constructor; auto. closed_rty_solver2.
    intros. rewrite rR_implies_overbase_simpl in H1; eauto; closed_rty_solver2.
Qed.

Lemma ctxrR2_under_over: forall Γ st b n d ϕ1 ϕ2,
  {st}⟦[v:b|n|d|ϕ2]⟧⊆⟦[v:b|n|d|ϕ1]⟧{Γ} <-> {st}⟦{v:b|n|d|ϕ1}⟧⊆⟦{v:b|n|d|ϕ2}⟧{Γ}.
Proof.
  induction Γ; split; intros.
  - invclear H; constructor; auto; try closed_rty_solver2.
    intros. rewrite rR_implies_under_iff_over in H3; auto; closed_rty_solver2.
  - invclear H; constructor; auto; try closed_rty_solver2.
    intros. rewrite <- rR_implies_under_iff_over in H3; auto; closed_rty_solver2.
  - invclear H; constructor; auto; try closed_rty_solver2.
    + intros. auto_under c_x. rewrite <- IHΓ; auto.
    + mydestr. exists x0; split; auto. intros. auto_under e_x. apply H0 in H7.
      rewrite <- IHΓ; auto.
    + mydestr. exists x0; split; auto. intros. auto_under e_x. apply H0 in H8.
      rewrite <- IHΓ; auto.
  - invclear H; constructor; auto; try closed_rty_solver2.
    + intros. auto_under c_x. rewrite IHΓ; auto.
    + mydestr. exists x0; split; auto. intros. auto_under e_x. apply H0 in H7.
      rewrite IHΓ; auto.
    + mydestr. exists x0; split; auto. intros. auto_under e_x. apply H0 in H8.
      rewrite IHΓ; auto.
Qed.

Lemma inv_ctxrR2_oarr: forall Γ x st b n d ϕ1 ϕ2 τ1 τ2,
    x ∉ stale τ2 ∪ stale τ1 ∪ stale d ∪ stale Γ ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom _ st) (-:{v: b | n | d | ϕ1}⤑ τ1) ->
    closed_rty 0 (ctxdom ⦑Γ⦒ ∪ dom _ st) (-:{v: b | n | d | ϕ2}⤑ τ2) ->
    {st}⟦{v:b|n|d|ϕ2}⟧⊆⟦{v:b|n|d|ϕ1}⟧{Γ} ->
    {st}⟦τ1^r^ x⟧⊆⟦τ2^r^ x⟧{Γ ++ [(x, {v:b|n|d|ϕ2})] } ->
    {st}⟦-:{v: b | n | d | ϕ1}⤑ τ1⟧⊆⟦-:{v: b | n |  d | ϕ2}⤑ τ2⟧{Γ}.
Proof.
  induction Γ; intros.
  { listctx_set_simpl.
    apply inv_ctxrR2_oarr_rR with (x:=x); eauto; try fast_set_solver; closed_rty_solver. }
  mydestr.
  assert (⌊ -:{v: b | n | d | ϕ1}⤑ τ1 ⌋ = ⌊ -:{v: b | n | d | ϕ2}⤑ τ2 ⌋) as HTeq.
  { simpl. apply ctxrR2_implies_erase_eq in H3. inv_rd_simpl0. rewrite H3; auto. }
  invclear H2; invclear H3; try auto_ty_exfalso.
  - constructor; auto. intros. auto_under c_x.
    apply IHΓ with (x:=x); try fast_set_solver; try closed_rty_solver.
  - constructor; auto. mydestr. auto_meet_exists HE. dsimp1.
    apply IHΓ with (x:=x); auto. fast_set_solver. closed_rty_solver. closed_rty_solver.
    + auto_meet_reduce. auto_under e_x; auto.
    + auto_meet_reduce. auto_under e_x; auto.
  - inv_rd_simpl1. constructor; auto. mydestr.
    assert ({st}⟦{v:b|n|d|ϕ2}⟧⊆⟦{v:b|n|d|ϕ1}⟧{Γ}).
    { auto_under x1.
      assert (∃ v : value, ({0;b∅;st}⟦r⟧) v ∧ x1 ↪* v) by (apply rR_arr_halt; auto).
      mydestr. assert ([] ⊢t x2 ⋮v ⌊ r ⌋ ). refinement_solver.
      eapply H5 in H15; eauto. denotation_simp. }
    exists x0. split; auto. intros. auto_under e_x.
    assert ([] ⊢t v_x ⋮v ⌊ r ⌋ ). refinement_solver. denotation_simp.
    apply IHΓ with (x:=x); try fast_set_solver.
Qed.

Lemma inv_ctxrR2_arrarr: forall Γ x st τ11 τ12 τ21 τ22,
    x ∉ stale τ11 ∪ stale τ12 ∪ stale τ21 ∪ stale τ22 ∪ stale Γ ->
    closed_rty 0 (ctxdom ⦑ Γ ⦒ ∪ dom _ st) (τ11 ⤑ τ12) ->
    closed_rty 0 (ctxdom ⦑ Γ ⦒ ∪ dom _ st) (τ21 ⤑ τ22) ->
    {st}⟦τ21⟧⊆⟦τ11⟧{Γ} ->
    {st}⟦τ12⟧⊆⟦τ22⟧{Γ} ->
    is_arr τ21 -> is_arr τ11 ->
    {st}⟦τ11 ⤑ τ12⟧⊆⟦τ21 ⤑ τ22⟧{Γ}.
Proof.
  induction Γ; intros.
  { listctx_set_simpl.
    apply inv_ctxrR2_arrarr_rR with (x:=x); eauto; try fast_set_solver; closed_rty_solver. }
  mydestr.
  assert (⌊ τ11 ⤑ τ12 ⌋ = ⌊ τ21 ⤑ τ22 ⌋) as HTeq.
  { simpl. apply ctxrR2_implies_erase_eq in H2. apply ctxrR2_implies_erase_eq in H3.
    rewrite H2. rewrite H3. auto. }
  (* simpl in H0. simpl in H1. *)
  (* rewrite decide_True in H0; auto. *)
  (* constructor; auto. admit. admit. *)
  invclear H2; invclear H3; try auto_ty_exfalso.
  - assert (closed_rty 0 ({[a]} ∪ ctxdom ⦑Γ⦒ ∪ dom aset st) (τ11 ⤑ τ12)) as CT1.
    { rewrite closed_rty_destruct_arrarr. split; auto. split; auto. split; auto. refinement_solver. }
    assert (closed_rty 0 ({[a]} ∪ ctxdom ⦑Γ⦒ ∪ dom aset st) (τ21 ⤑ τ22)) as CT2.
    { rewrite closed_rty_destruct_arrarr. split; auto. split; auto. split; auto. refinement_solver. }
    simpl in H0. simpl in H1.
    constructor; auto.
    intros. auto_under c_x.
    apply IHΓ with (x:=x); try fast_set_solver; try closed_rty_solver.
  - constructor; auto. mydestr. auto_meet_exists HE. dsimp1.
    apply IHΓ with (x:=x); auto. fast_set_solver. closed_rty_solver. closed_rty_solver.
    + auto_meet_reduce. auto_under e_x; auto.
    + auto_meet_reduce. auto_under e_x; auto.
  - inv_rd_simpl1. constructor; auto. mydestr.
    assert ({st}⟦τ21⟧⊆⟦τ11⟧{Γ}).
    { auto_under x1.
      assert (∃ v : value, ({0;b∅;st}⟦r⟧) v ∧ x1 ↪* v) by (apply rR_arr_halt; auto).
      mydestr. assert ([] ⊢t x2 ⋮v ⌊ r ⌋ ). refinement_solver.
      eapply H7 in H17; eauto. denotation_simp. }
    exists x0. split; auto. intros. auto_under e_x.
    assert ([] ⊢t v_x ⋮v ⌊ r ⌋ ). refinement_solver. denotation_simp.
    apply IHΓ with (x:=x); try fast_set_solver.
Qed.
