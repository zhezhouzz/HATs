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
Import TermOrdering.

Global Hint Constructors ok_dctx: core.

Lemma rR_implies_no_free: forall st e τ a, ({0;b∅;st}⟦τ⟧) e -> a ∉ fv_tm e.
Proof.
  intros. refinement_solver7. basic_typing_solver7. set_solver.
Qed.

Global Hint Resolve rR_implies_no_free: core.

Lemma ctxrR_tlete_drop_halt_lhs: forall st τ τ_x a e_x e,
    not_overbasety τ ->
   {0;b∅;st}⟦τ⟧ e -> {0;b∅;st}⟦τ_x⟧ e_x ->
   (∃ v : value, e_x ↪* v) ->
   ({0;b∅;st}⟦τ⟧) (tlete e_x (a \t\ e)).
Proof.
  intros.
  eapply termR_perserve_rR; eauto; refinement_solver7.
  eapply termR_tlete_drop_halt_lhs'; refinement_solver7.
Qed.

Global Hint Resolve ctxrR_tlete_drop_halt_lhs: core.

Lemma rR_implies_reduction_no_free: forall st r e (v: value),
    ({0;b∅;st}⟦r⟧) e -> e ↪* v -> closed_value v.
Proof.
  intros.
  assert ([] ⊢t v ⋮v ⌊ r ⌋);eauto. refinement_solver.
Qed.

Global Hint Resolve rR_implies_reduction_no_free: core.

Global Hint Resolve is_arr_implies_not_overbasety: core.

Lemma is_arr_simpl_rewrite: forall r a st (P: state -> tm -> Prop),
    is_arr r ->
    closed_rty 0 (dom aset st) r ->
    (∀ e_wf : tm, ({0;b∅;st}⟦r⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) ->
    (∃ e_x_hat : tm, ({0;b∅;st}⟦r⟧) e_x_hat
                     ∧ (∀ e_x : tm, ({0;b∅;st}⟦r⟧) e_x → ∀ v_x : value, e_x_hat ↪* v_x → P ({a↦v_x} st) e_x)) <->
      (∀ e_x : tm, ({0;b∅;st}⟦r⟧) e_x → P st e_x).
Proof.
  split; intros.
  - mydestr. assert (∃ v_x : value, x ↪* v_x); auto. mydestr.
    eapply H4 in H3; eauto.
    assert ([] ⊢t x0 ⋮v ⌊r⌋). refinement_solver7.
    assert (closed_value x0) as Hclosedv. basic_typing_solver.
    apply state_insert_closed_value with (a:=a) (st:=st) in Hclosedv.
    destruct Hclosedv; mydestr; subst.
    + invclear H6. destruct r; destruct x1; inversion H; invclear H9.
    + rewrite <- H7; auto.
  - exists (random_inhabitant r).
    assert ({0;b∅;st}⟦r⟧ (random_inhabitant r)).
    apply random_inhabitant_in_any_under; refinement_solver7.
    split; auto. intros.
    assert ([] ⊢t v_x ⋮v ⌊r⌋) by refinement_solver7.
    assert (closed_value v_x) as Hclosedv. basic_typing_solver.
    apply state_insert_closed_value with (a:=a) (st:=st) in Hclosedv.
    destruct Hclosedv; mydestr; subst.
    + invclear H6. destruct r; destruct x; inversion H; invclear H9.
    + rewrite H7; auto.
Qed.

Lemma is_arr_simpl_rewrite_value: forall r a st (P: state -> tm -> Prop),
    is_arr r ->
    closed_rty 0 (dom aset st) r ->
    (∀ e_wf : tm, ({0;b∅;st}⟦r⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) ->
    (∃ e_x_hat : tm, ({0;b∅;st}⟦r⟧) e_x_hat
                     ∧ (∀ e_x : value, ({0;b∅;st}⟦r⟧) e_x → ∀ v_x : value, e_x_hat ↪* v_x → P ({a↦v_x} st) e_x)) <->
      (∀ e_x : value, ({0;b∅;st}⟦r⟧) e_x → P st e_x).
Proof.
  split; intros.
  - mydestr. assert (∃ v_x : value, x ↪* v_x); auto. mydestr.
    eapply H4 in H3; eauto.
    assert ([] ⊢t x0 ⋮v ⌊r⌋). refinement_solver7.
    assert (closed_value x0) as Hclosedv. basic_typing_solver.
    apply state_insert_closed_value with (a:=a) (st:=st) in Hclosedv.
    destruct Hclosedv; mydestr; subst.
    + invclear H6. destruct r; destruct x1; inversion H; invclear H9.
    + rewrite <- H7; auto.
  - exists (random_inhabitant r).
    assert ({0;b∅;st}⟦r⟧ (random_inhabitant r)).
    apply random_inhabitant_in_any_under; refinement_solver7.
    split; auto. intros.
    assert ([] ⊢t v_x ⋮v ⌊r⌋) by refinement_solver7.
    assert (closed_value v_x) as Hclosedv. basic_typing_solver.
    apply state_insert_closed_value with (a:=a) (st:=st) in Hclosedv.
    destruct Hclosedv; mydestr; subst.
    + invclear H6. destruct r; destruct x; inversion H; invclear H9.
    + rewrite H7; auto.
Qed.

Lemma under_not_overbasety: forall x1 x2 x3 x4, not_overbasety [v:x1|x2|x3|x4].
Proof.
  simpl; auto.
Qed.

Global Hint Resolve under_not_overbasety: core.


Lemma rR_implies_reduction_no_free_unfold
     : ∀ (st : state) (r : rty) (e : tm) (v : value), ({0;b∅;st}⟦r⟧) e → e ↪* v → fv_value v ≡ ∅.
Proof.
  intros. eapply rR_implies_reduction_no_free in H; eauto.
Qed.

Global Hint Resolve rR_implies_reduction_no_free_unfold: core.

Lemma rR_implies_no_free_value_unfold
     : ∀ (st : state) (r : rty) (v : value), ({0;b∅;st}⟦r⟧) v → fv_value v ≡ ∅.
Proof.
  intros.
  assert ([] ⊢t v ⋮v ⌊ r ⌋); refinement_solver.
Qed.

Global Hint Resolve rR_implies_no_free_value_unfold: core.

Lemma rR_implies_no_free_value
     : ∀ (st : state) (r : rty) (v : value), ({0;b∅;st}⟦r⟧) v → closed_value v.
Proof.
  intros. unfold closed_value. eapply rR_implies_no_free_value_unfold; eauto.
Qed.

Global Hint Resolve rR_implies_no_free_value: core.

Ltac lc_simpl3 :=
  simpl;
  repeat (match goal with
          | [H: ?x ∉ fv_tm ?e_x, H': context [ {?x := _ }t ?e_x] |- _ ] =>
              rewrite (subst_fresh_tm e_x x) in H'; auto
          | [H: ?x ∉ fv_tm ?e_x |- context [ {?x := _ }t ?e_x] ] =>
              rewrite (subst_fresh_tm e_x x); auto
          | [H: ({0;b∅;_}⟦ _ ⟧) ?e_x, H': context [ {?x := _ }t ?e_x] |- _ ] =>
              assert (x ∉ fv_tm e_x) as Htmp by (eauto; refinement_solver);
              rewrite (subst_fresh_tm e_x x) in H'; auto; try clear Htmp
          | [H: ({0;b∅;_}⟦ _ ⟧) ?e_x |- context [ {?x := _ }t ?e_x] ] =>
              assert (x ∉ fv_tm e_x) as Htmp by (eauto; refinement_solver);
              rewrite (subst_fresh_tm e_x x); auto; try clear Htmp
          | [H: ({0;b∅;_}⟦ _ ⟧) (tvalue ?e_x), H': context [ {?x := _ }v ?e_x] |- _ ] =>
              assert (x ∉ fv_tm e_x) as Htmp by (eauto; refinement_solver);
              rewrite (subst_fresh_value e_x x) in H'; auto; try clear Htmp
          | [H: ({0;b∅;_}⟦ _ ⟧) (tvalue ?e_x) |- context [ {?x := _ }v ?e_x] ] =>
              assert (x ∉ fv_tm e_x) as Htmp by (eauto; refinement_solver);
              rewrite (subst_fresh_value e_x x); auto; try clear Htmp
          | [|- context [ {?x := _ }t (?x \t\ _) ] ] => rewrite close_then_subst_same_tm
          | [H: context [ {?x := _ }t (?x \t\ _) ] |- _ ] => rewrite close_then_subst_same_tm in H
          | [|- context [ {?x := _ }v (?x \v\ _) ] ] => rewrite close_then_subst_same_value
          | [H: context [ {?x := _ }v (?x \v\ _) ] |- _ ] => rewrite close_then_subst_same_value in H
          end).

Ltac ctx_rm_simp1 :=
  repeat
    match goal with
    | [H: context [⦑(_, _) :: _⦒] |- _ ] => simpl in H; try dec_solver2
    | [|- context [⦑(_, _) :: _⦒] ] => simpl; try dec_solver2
    | [H: context [⦑ ?a ++ ?b ⦒] |- _ ] => setoid_rewrite (ctx_rm_app a b) in H
    | [|- context [⦑ ?a ++ ?b ⦒] ] => setoid_rewrite (ctx_rm_app a b)
    | [H: context [ctxdom ((_, _) :: _)] |- _] => simpl in H
    | [|- context [ctxdom ((_, _) :: _)]] => simpl
    | [H: context [ctxdom (_ ++ _)] |- _] =>  setoid_rewrite ctxdom_app_union in H
    | [|- context [ctxdom (_ ++ _)]] =>  setoid_rewrite ctxdom_app_union
    end.

Lemma rR_arr_halt: forall m bst st τ e,
    is_arr τ -> {m;bst;st}⟦τ⟧ e -> (exists (v: value), {m;bst;st}⟦τ⟧ v /\ e ↪* v).
Proof.
  intros. destruct τ; try auto_ty_exfalso.
  - simpl in H0; mydestr. exists x; split; auto.
    constructor; auto. reduction_solver1. split; auto.
    eexists; split; eauto. reduction_solver1.
  - simpl in H0; mydestr. exists x; split; auto.
    constructor; auto. reduction_solver1. split; auto.
    eexists; split; eauto. reduction_solver1.
Qed.

Lemma rR_arrow_value_lam_exists_oarr:
  ∀ (v : value) b n d ϕ τ m bst st,
    {m;bst;st}⟦-:{v: b | n | d | ϕ}⤑ τ⟧ v ->
    (∃ e : tm, v = vlam b e) ∨ (∃ e : tm, v = vfix (b ⤍ ⌊ τ ⌋) (vlam b e)).
Proof.
  intros.
  apply empty_basic_typing_arrow_value_lam_exists. refinement_solver.
Qed.

Lemma rR_arrow_value_lam_exists_arrarr:
  ∀ (v : value) τ_x τ m bst st,
    {m;bst;st}⟦τ_x ⤑ τ⟧ v ->
    (∃ e : tm, v = vlam ⌊ τ_x ⌋ e) ∨ (∃ e : tm, v = vfix (⌊ τ_x ⌋ ⤍ ⌊ τ ⌋) (vlam ⌊ τ_x ⌋ e)).
Proof.
  intros.
  apply empty_basic_typing_arrow_value_lam_exists. refinement_solver.
Qed.

Lemma open_subst_same_rset: forall x (v: constant) d, x ∉ d -> refinement_set_subst x v ({[x]} ∪ d) = d.
Proof.
  intros. unfold refinement_set_subst. dec_solver2. set_solver.
Qed.

Lemma open_subst_same_r: forall x (v: constant) d k (ϕ: refinement),
    x ∉ d -> not_fv_in_refinement d ϕ ->
      refinement_subst x v ({[x]} ∪ d) (refinement_open k x ϕ) = refinement_open k v ϕ.
Proof.
  intros. unfold refinement_subst. unfold refinement_open. unfold state_subst.
  apply prop_ex3. intros.
  dec_solver2. my_simplify_map_eq3.
  apply H0. intros. my_simplify_map_eq3.
Qed.

Lemma open_subst_same_rty: forall x (v: constant) τ k,
    valid_rty τ ->
    x # (rty_fv τ) -> {x := v }r ({k ~r> x} τ) = {k ~r> v} τ.
Proof.
  intros x v. induction τ; simpl; intros.
  - rewrite open_subst_same_rset; auto. setoid_rewrite open_subst_same_r; auto.
    invclear H. invclear H2; auto.
  - rewrite open_subst_same_rset; auto. setoid_rewrite open_subst_same_r; auto.
    invclear H. invclear H2; auto.
  - rewrite open_subst_same_rset; auto; try fast_set_solver.
    setoid_rewrite open_subst_same_r; auto; try fast_set_solver.
    rewrite IHτ; auto; refinement_solver. valid_solver.
  - rewrite IHτ1; auto; refinement_solver.
    rewrite IHτ2; auto; refinement_solver.
Qed.

Lemma opened_term_tyable_renaming: forall Γ x Tx e T,
    x ∉ fv_tm e ->
    (Γ ++ [(x, Tx)]) ⊢t e ^t^ x ⋮t T ->
    Γ ⊢t vlam Tx e ⋮v Tx ⤍ T.
Proof.
  intros. auto_exists_L; simpl; intros.
  apply basic_has_type_renaming with (x0:=x0) in H0.
  rewrite open_subst_same_tm in H0; auto.
  fast_set_solver. basic_typing_solver.
Qed.

Lemma closed_rty_implies_weak_bound_in_refinement_over: forall m L b n d ϕ,
   closed_rty m L {v:b|n|d|ϕ} -> bound_in_refinement m ϕ.
Proof.
  intros. invclear H. invclear H0. invclear H3. invclear H1.
  unfold bound_in_refinement in H0. unfold bound_in_refinement. intros. apply H0.
  eapply bst_eq_trans; eauto.
Qed.

Lemma closed_rty_implies_weak_bound_in_refinement_under: forall m L b n d ϕ,
   closed_rty m L [v:b|n|d|ϕ] -> bound_in_refinement m ϕ.
Proof.
  intros. invclear H. invclear H0. invclear H3. invclear H1.
  unfold bound_in_refinement in H0. unfold bound_in_refinement. intros. apply H0.
  eapply bst_eq_trans; eauto.
Qed.

From Coq Require Import Logic.FunctionalExtensionality.

Lemma bstate_insert_push: forall m (c c_x: constant) bst, (<b[S m:=c]> (<b[↦c_x]> bst)) = (<b[↦c_x]> (<b[m:=c]> bst)).
Proof.
  unfold bstate_push; unfold bstate_insert; intros.
  apply functional_extensionality. intros.
  destruct x; repeat dec_solver2. invclear e. exfalso. apply n; auto.
Qed.

Lemma bst_eq_push: forall m (c_x: constant) bst bst',
    bst_eq m bst bst' ->
    bst_eq (S m) (<b[↦c_x]> bst) (<b[↦c_x]> bst').
Proof.
  unfold bst_eq; unfold bstate_push; intros.
  destruct i; auto. apply H. lia.
Qed.

Ltac inv_rd_simpl0 :=
  progress repeat
    (ctx_erase_simp;
     listctx_set_simpl;
     ctx_rm_simp1;
     my_simplify_map_eq3;
     basic_typing_simpl1;
     repeat match goal with
       | [H: context [ ⌊{_ ~r> _} _ ⌋ ] |- _ ] => rewrite rty_open_perserve_erase in H
       | [|- context [ ⌊{_ ~r> _} _ ⌋ ]] => rewrite rty_open_perserve_erase
       | [H: closed_rty _ _ ?τ |- _ ∉ rty_fv ?τ ] => invclear H
       end).

Lemma rR_open_trans': forall τ m bst bst' st (c: constant) e,
    bst_eq (S m) (<b[m:=c]> bst) bst' ->
    (closed_rty (S m) (dom aset st) τ /\ ({m;bst;st}⟦{m ~r> c} τ⟧) e) <-> ({S m;bst';st}⟦τ⟧) e.
Proof.
  induction τ; split; intros; mydestr.
  - invclear H1; mydestr. do 2 (split; auto).
    eexists; split; eauto. split; auto. subst.
    apply closed_rty_implies_weak_bound_in_refinement_over in H0.
    eapply H0 in H. rewrite <- H; eauto.
  - invclear H0; mydestr; subst. do 3 (split; auto).
    + apply closed_rty_open_trans with (c:=c) in H0; auto.
    + eexists; split; eauto. split; auto.
      apply closed_rty_implies_weak_bound_in_refinement_over in H0.
      eapply H0 in H. rewrite <- H in H3; eauto.
  - invclear H1; mydestr. do 2 (split; auto).
    intros. apply H3; auto.
    apply closed_rty_implies_weak_bound_in_refinement_under in H0.
    eapply H0 in H. rewrite <- H in H5; eauto.
  - invclear H0; mydestr. do 3 (split; auto).
    + apply closed_rty_open_trans with (c:=c) in H0; auto.
    + intros. apply H2; auto.
      apply closed_rty_implies_weak_bound_in_refinement_under in H0.
      eapply H0 in H. rewrite <- H; eauto.
  - invclear H1; mydestr. simpl in H2. simpl in H1. inv_rd_simpl0. do 2 (split; auto).
    eexists; split; eauto.
    intros. apply IHτ with (c:=c) (bst:= (<b[↦c_x]> bst)); eauto.
    + rewrite bstate_insert_push. apply bst_eq_push; auto.
    + rewrite closed_rty_destruct_oarr in H0; mydestr. split; auto.
      apply H4; auto.
      apply closed_rty_implies_weak_bound_in_refinement_over in H0.
      eapply H0 in H. rewrite <- H in H6; eauto.
  - invclear H0; mydestr. inv_rd_simpl0. do 3 (split; auto).
    apply closed_rty_open_trans with (c:=c) in H0; auto.
    eexists; split; eauto.
    intros. rewrite closed_rty_destruct_oarr in H0; mydestr.
    assert (ϕ bst' st c_x) as Hz.
    { apply closed_rty_implies_weak_bound_in_refinement_over in H0.
      eapply H0 in H. rewrite <- H; eauto. }
    apply H3 in Hz; auto. rewrite <- IHτ in Hz; mydestr; eauto.
    rewrite bstate_insert_push. apply bst_eq_push; auto.
  - invclear H1; mydestr. simpl in H2. inv_rd_simpl0. do 2 (split; auto).
    eexists; split; eauto.
    intros. rewrite closed_rty_destruct_arrarr in H0; mydestr.
    eapply IHτ2; eauto. split; auto. apply H4. rewrite <- IHτ1 in H5; mydestr; eauto.
  - invclear H0; mydestr. simpl in H1. inv_rd_simpl0. do 3 (split; auto).
    apply closed_rty_open_trans with (c:=c) in H0; auto.
    eexists; split; eauto.
    intros. rewrite closed_rty_destruct_arrarr in H0; mydestr.
    assert (({S m;bst';st}⟦τ1⟧) v_x) as Hz by (rewrite <- IHτ1; eauto).
    apply H3 in Hz. rewrite <- IHτ2 in Hz; mydestr; eauto.
Qed.

Lemma rR_open_trans_empty: forall τ st (c: constant) e,
    closed_rty 1 (dom aset st) τ ->
    ({0;b∅;st}⟦τ ^r^ c⟧) e -> {1;<b[↦c]> b∅;st}⟦τ⟧ e.
Proof.
  intros. rewrite <- rR_open_trans'; eauto.
  unfold bst_eq; intros. destruct i; auto.
Qed.

Lemma ctxfind_get_last: forall a B Γ x τ_x,
    ok ((a, B) :: ⌊Γ ++ [(x, τ_x)]⌋*) ->
    ctxfind ((a, B) :: ⌊Γ ++ [(x, τ_x)]⌋*) x = Some ⌊τ_x⌋.
Proof.
  intros.
  assert (x <> a). ctx_erase_simp.  basic_typing_solver8.
  repeat dec_solver2. ctx_erase_simp. apply ctxfind_last_eq. ctx_erase_simp.
Qed.

Lemma var_last_typable: forall a B Γ x τ_x,
    ok ((a, B) :: ⌊Γ ++ [(x, τ_x)]⌋*) -> ((a, B) :: ⌊Γ ++ [(x, τ_x)]⌋*) ⊢t x ⋮t ⌊τ_x⌋.
Proof.
  intros. constructor; auto. constructor; auto. apply ctxfind_get_last; auto.
Qed.

Lemma closed_rty_mk_eq_var: forall b x, closed_rty 0 ({[x]}) (mk_eq_var b x).
Proof.
  intros. constructor; eauto.
  - do 2 (constructor; auto).
    + unfold not_fv_in_refinement. intros. rewrite H; fast_set_solver.
    + unfold bound_in_refinement. auto.
  - constructor; auto.
Qed.

Lemma reduction_implies_termR: forall e e' T, e ↪* e' -> [] ⊢t e ⋮t T -> e' <-<{ []; T} e.
Proof.
  intros. constructor; auto.
  - eapply multi_preservation; eauto.
  - unfold termRraw. intros Γv. intros. invclear H1. simpl. simpl in H2.
    eapply multistep_trans; eauto.
Qed.

Definition riv (τ: rty): value :=
  match τ with
  | {v: _ | _ | _ | _ } => 0
  | [v: _ | _ | _ | _ ] => 0
  | -:{v: T1 | _ | _ | _ } ⤑ τ => vlam T1 (random_inhabitant τ)
  | τ1 ⤑ τ2 => vlam (rty_erase τ1) (random_inhabitant τ2)
  end.

Global Hint Resolve lc_implies_body_tm: core.

Lemma lc_riv: forall τ, lc (riv τ).
Proof.
  intros. destruct τ; simpl; auto.
  - rewrite lc_abs_iff_body; auto.
  - rewrite lc_abs_iff_body; auto.
Qed.

Global Hint Resolve lc_riv: core.

Lemma riv_in_any_under: ∀ (τ : rty) (bst : bstate) (n : nat) (st : state),
    is_arr τ → closed_rty n (dom aset st) τ → ({n;bst;st}⟦τ⟧) (riv τ).
Proof.
  intros. destruct τ; auto_ty_exfalso.
  - apply random_inhabitant_in_any_under; refinement_solver7.
  - apply random_inhabitant_in_any_under; refinement_solver7.
Qed.

Ltac lc_solver_r :=
  match goal with
  | [H: ?x ∉ fv_tm ?e |- ?x ∉ fv_tm ({_ := _ }t ?e)] =>
      rewrite fv_of_subst_tm_closed; refinement_solver
  end.

Lemma bound_in_refinement_open_minus1: forall n (v1: value) ϕ,
    ((exists (n: constant), v1 = n) \/ (exists (y: atom), v1 = y)) ->
    bound_in_refinement (S n) ϕ -> bound_in_refinement n (refinement_open n v1 ϕ).
Proof.
  unfold bound_in_refinement; unfold refinement_open. intros. destruct H; mydestr; subst.
  - apply H0. apply bst_eq_insert_S; auto.
  - destruct (st !! x).
    + apply H0. apply bst_eq_insert_S; auto.
    + apply H0. apply bst_eq_insert_S; auto.
Qed.

Lemma state_subst_implies_rty_subst_eq2_forward_closed_rty
  : ∀ (a v: atom) (L d: aset) (c_x : constant)
      (k : nat) (b : base_ty) (m n : nat) (ϕ : refinement),
    not_fv_in_refinement d ϕ -> bound_in_refinement (n `min` k) (refinement_open k c_x ϕ) ->
    closed_rty m L ({k ~r> v} [v:b|n|d|ϕ]) ->
    closed_rty m L ({k ~r> {a := c_x }v v} [v:b|n|d|ϕ]).
Proof.
  intros. destruct (decide (a = v)); subst; auto; biop_simpl; auto.
  invclear H1. constructor; auto.
  - constructor; auto. constructor; auto.
    unfold not_fv_in_refinement. unfold refinement_open. intros.
    apply H; auto.
  - invclear H3. constructor; auto.
  - simpl in H4. simpl. fast_set_solver.
Qed.

Lemma state_subst_implies_rty_subst_eq2_rR
  : ∀ (a v: atom) st bst (c_x : constant)
      (k : nat) (b : base_ty) m (n : nat) (d : aset) (ϕ : refinement) e,
    (closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> {a := c_x }v v} [v:b|n|d|ϕ]) /\
       {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> v} [v:b|n|d|ϕ]⟧ e) <->
      (closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> v} [v:b|n|d|ϕ]) /\
         {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> {a := c_x }v v} [v:b|n|d|ϕ] ⟧ e).
Proof.
  split; intros; mydestr.
  - split; auto. refinement_solver.
    destruct (decide (a = v)); subst; auto; biop_simpl; auto.
    invclear H0; mydestr. constructor; auto. split; auto.
    intros. apply H2; auto. unfold refinement_open. my_simplify_map_eq3.
  - split; auto. refinement_solver.
    destruct (decide (a = v)); subst; auto; biop_simpl; auto.
    invclear H0; mydestr. constructor; auto. split; auto.
    intros. apply H2; auto. unfold refinement_open in H4.
    my_simplify_map_eq3.
Qed.

Lemma state_subst_implies_rty_subst_eq2_rR_forward
  : ∀ (a v: atom) st bst (c_x : constant)
      (k : nat) (b : base_ty) m (n : nat) (d : aset) (ϕ : refinement) e,
    closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> {a := c_x }v v} [v:b|n|d|ϕ]) ->
    {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> v} [v:b|n|d|ϕ]⟧ e ->
    {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> {a := c_x }v v} [v:b|n|d|ϕ] ⟧ e.
Proof.
  intros.
  assert (closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> {a := c_x }v v} [v:b|n|d|ϕ]) /\
         {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> v} [v:b|n|d|ϕ]⟧ e); auto.
  rewrite state_subst_implies_rty_subst_eq2_rR in H1; mydestr; auto.
Qed.

Lemma state_subst_implies_rty_subst_eq2_rR_backward
  : ∀ (a v: atom) st bst (c_x : constant)
      (k : nat) (b : base_ty) m (n : nat) (d : aset) (ϕ : refinement) e,
    closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> v} [v:b|n|d|ϕ]) ->
    {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> {a := c_x }v v} [v:b|n|d|ϕ] ⟧ e ->
    {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> v} [v:b|n|d|ϕ]⟧ e.
Proof.
  intros.
  assert (closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> v} [v:b|n|d|ϕ]) /\
         {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> {a := c_x }v v} [v:b|n|d|ϕ] ⟧ e); auto.
  rewrite <- state_subst_implies_rty_subst_eq2_rR in H1; mydestr; auto.
Qed.

Lemma state_insert_include_a: forall (a: atom) (st: state) (c_x: constant),
    a ∈ dom aset (<[a:=c_x]> st).
Proof.
  intros. rewrite dom_insert_simp; auto. set_solver.
Qed.

Global Hint Resolve state_insert_include_a: core.

Lemma tletbiop_aux6: forall op (v1 v2: value),
    ((exists (n: constant), v1 = n) \/ (exists (y: atom), v1 = y)) ->
    ((exists (n: constant), v2 = n) \/ (exists (y: atom), v2 = y)) ->
    bound_in_refinement 0
      (refinement_open 1 v1
         (refinement_open 0 v2
            (λ (bst : bstate) (_ : state) (v : constant), eval_op op (bst 0) (bst 1) v))).
Proof.
  unfold bound_in_refinement; unfold refinement_open. intros.
  destruct H; destruct H0; mydestr;
    try (try destruct (st !! x); auto; try destruct (st !! x0); subst; auto);
    try (destruct (st !! x); auto);
    try (destruct (st !! x0); auto).
Qed.

Lemma tletbiop_aux7: forall op (v1 v2: value),
    ((exists (n: constant), v1 = n) \/ (exists (y: atom), v1 = y)) ->
    ((exists (n: constant), v2 = n) \/ (exists (y: atom), v2 = y)) ->
    bound_in_refinement 0
      (refinement_open 0 v1
         (refinement_open 1 v2
            (λ (bst : bstate) (_ : state) (v : constant), eval_op op (bst 0) (bst 1) v))).
Proof.
  unfold bound_in_refinement; unfold refinement_open. intros.
  destruct H; destruct H0; mydestr;
    try (try destruct (st !! x); auto; try destruct (st !! x0); subst; auto);
    try (destruct (st !! x); auto);
    try (destruct (st !! x0); auto).
Qed.

Lemma tletbiop_aux8: forall (d: aset), (d ∪ ∅) = d.
Proof.
  intros. set_solver. Qed.

Lemma not_fv_in_refinement_aux: forall op (v: value) (n: nat),
    n ≤ 1 -> ((exists (n: constant), v = n) \/ (exists (y: atom), v = y)) ->
    not_fv_in_refinement (fv_value v)
      (refinement_open n v
         (λ (bst : bstate) (_ : state) (v : constant), eval_op op (bst 0) (bst 1) v)).
Proof.
  unfold not_fv_in_refinement; unfold refinement_open. intros.
  destruct H0; mydestr; subst; auto.
  assert (m !! x = m' !! x). apply H1; fast_set_solver. rewrite H0.
  destruct (m'!!x); auto.
Qed.

Lemma letebiop_aux9: forall op r, is_arr r -> ~ ⌊r⌋ = fst_ty_of_op op.
Proof.
  intros. destruct r; destruct op; simpl; invclear H; try (intro H; invclear H).
Qed.

Lemma rR_open_trans_empty': forall τ st (c: constant) e,
    {1;<b[↦c]> b∅;st}⟦τ⟧ e -> ({0;b∅;st}⟦τ ^r^ c⟧) e.
Proof.
  intros. rewrite <- rR_open_trans' in H; mydestr; eauto.
  unfold bst_eq. intros. assert (i = 0). lia. subst. simpl. unfold bstate_insert. dec_solver2.
Qed.

Lemma rR_base_implies_constant: forall m bst st b1 n1 d1 ϕ1 (c2: value),
  ({m;bst;st}⟦[v:b1|n1|d1|ϕ1]⟧) c2 -> (exists c: constant, c2 = c).
Proof.
  intros. apply rR_regular1 in H. mydestr. invclear H0. invclear H3; eauto. invclear H1.
Qed.

Global Hint Resolve rR_base_implies_constant: core.

Ltac inv_rd_simpl3 :=
  repeat match goal with
    | [H: context [⌊[v:_|_|_|_]⌋] |- _ ] => simpl in H
    | [H: context [⌊{v:_|_|_|_}⌋] |- _ ] => simpl in H
    | [H: context [⌊-:{v: _|_|_|_}⤑ _⌋] |- _ ] => simpl in H
    | [H: context [⌊ _ ⤑ _⌋] |- _ ] => simpl in H
    | [H: context [ ⌊ (_, _) :: _ ⌋* ] |- _ ] => simpl in H
    | [|- context [⌊[v:_|_|_|_]⌋] ] => simpl
    | [|- context [⌊{v:_|_|_|_}⌋] ] => simpl
    | [|- context [⌊-:{v: _|_|_|_}⤑ _⌋] ] => simpl
    | [|- context [⌊ _ ⤑ _⌋] ] => simpl
    | [|- context [ ⌊ (_, _) :: _ ⌋* ] ] => simpl
    end.

Ltac reduction_simpl0 :=
  repeat match goal with
  | [H: tvalue _ ↪* tvalue _ |- _ ] =>
      rewrite value_reduce_to_value_implies_same in H; mydestr; subst
  end.


Lemma state_subst_implies_rty_subst_ok_dctx_all_v_to_c
  : ∀ (a: atom) (Γ : list (atom * rty)) (L : aset) (c_x : constant) (x : atom)
      (k : nat) τ,
    a ∉ stale Γ ∪ {[x]} ->
    closed_rty 0 (ctxdom ⦑ Γ ⦒ ∪ L) ({k ~r> c_x} τ) ->
    ok_dctx L (Γ ++ [(x, {k ~r> a} τ)]) ->
    ok_dctx L (Γ ++ [(x, {k ~r> c_x} τ)]).
Proof.
  intros a.
  induction Γ; intros.
  - denotation_simp.
    destruct (decide (is_arr τ)); invclear H1; try auto_ty_exfalso.
    + apply ok_dctx_cons_arr; auto; refinement_solver.
    + constructor; auto; refinement_solver.
  - denotation_simp. invclear H1.
    + constructor; auto. listctx_set_solver. apply IHΓ; auto. fast_set_solver.
      dec_solver2. refinement_solver.
    + apply ok_dctx_cons_arr; auto; refinement_solver. apply IHΓ; auto. fast_set_solver.
      dec_solver2.
Qed.

Lemma state_subst_implies_rty_subst_ok_dctx_all_c_to_v
  : ∀ (a: atom) (Γ : list (atom * rty)) (L : aset) (c_x : constant) (x : atom)
      (k : nat) τ,
    a ∉ stale Γ ∪ {[x]} ->
    closed_rty 0 (ctxdom ⦑ Γ ⦒ ∪ L) ({k ~r> a} τ) ->
    ok_dctx L (Γ ++ [(x, {k ~r> c_x} τ)]) ->
    ok_dctx L (Γ ++ [(x, {k ~r> a} τ)]).
Proof.
  intros a.
  induction Γ; intros.
  - denotation_simp.
    destruct (decide (is_arr τ)); invclear H1; try auto_ty_exfalso.
    + apply ok_dctx_cons_arr; auto; refinement_solver.
    + constructor; auto; refinement_solver.
  - denotation_simp. invclear H1.
    + constructor; auto. listctx_set_solver. eapply IHΓ; eauto. fast_set_solver.
      dec_solver2. refinement_solver.
    + apply ok_dctx_cons_arr; auto; refinement_solver. eapply IHΓ; eauto. fast_set_solver.
      dec_solver2.
Qed.

Lemma state_subst_implies_rty_subst_ok_dctx_all
  : ∀ (a v : atom) (Γ : list (atom * rty)) (L : aset) (c_x : constant) (x : atom)
      (k : nat) τ,
    a ∉ stale Γ ∪ {[x]} ->
    closed_rty 0 (ctxdom ⦑ Γ ⦒ ∪ L) ({k ~r> {a := c_x }v v} τ) ->
    ok_dctx L (Γ ++ [(x, {k ~r> v} τ)]) ->
    ok_dctx L (Γ ++ [(x, {k ~r> {a := c_x }v v} τ)]).
Proof.
  intros. destruct (decide (a = v)); subst; auto; simpl; dec_solver2.
  eapply state_subst_implies_rty_subst_ok_dctx_all_v_to_c; eauto.
  simpl in H0. rewrite decide_True in H0; auto.
Qed.

Lemma state_subst_implies_rty_subst_ok_dctx_all'
  : ∀ (a v : atom) (Γ : list (atom * rty)) (L : aset) (c_x : constant) (x : atom)
      (k : nat) τ,
    a ∉ stale Γ ∪ {[x]} ->
    closed_rty 0 (ctxdom ⦑ Γ ⦒ ∪ L) ({k ~r> v} τ) ->
    ok_dctx L (Γ ++ [(x, {k ~r> {a := c_x }v v} τ)]) ->
    ok_dctx L (Γ ++ [(x, {k ~r> v} τ)]).
Proof.
  intros. destruct (decide (a = v)); subst; auto.
  - simpl in H1. rewrite decide_True in H1; auto.
    eapply state_subst_implies_rty_subst_ok_dctx_all_c_to_v; eauto.
  - simpl in H1. dec_solver2.
Qed.

Lemma state_subst_implies_r_susbt_eq_forward
     : ∀ (k : nat) (a : atom) (ϕ : refinement) (bst : bstate) (st : state)
         (c_x v : constant),
         refinement_open k a ϕ bst (<[a:=c_x]> st) v ->
         refinement_open k c_x ϕ bst (<[a:=c_x]> st) v.
Proof.
  intros. rewrite <- state_subst_implies_r_susbt_eq; auto.
Qed.

Global Hint Resolve state_subst_implies_r_susbt_eq_forward: core.

Lemma state_subst_implies_r_susbt_eq_backward
     : ∀ (k : nat) (a : atom) (ϕ : refinement) (bst : bstate) (st : state)
         (c_x v : constant),
    refinement_open k c_x ϕ bst (<[a:=c_x]> st) v ->
    refinement_open k a ϕ bst (<[a:=c_x]> st) v.
Proof.
  intros. rewrite state_subst_implies_r_susbt_eq; auto.
Qed.

Global Hint Resolve state_subst_implies_r_susbt_eq_backward: core.

Lemma closed_rty_1_open_eq_0: forall τ (k: nat) (L:aset) (c: constant),
    closed_rty (S k) L τ -> closed_rty k L ({k ~r> c} τ).
Proof.
  induction τ; intros.
  - invclear H. constructor; auto.
  - invclear H. constructor; auto.
  - rewrite closed_rty_destruct_oarr in H; mydestr.
    simpl.
    rewrite closed_rty_destruct_oarr. split; auto.
    assert (closed_rty k L ({k ~r> c} {v:B|n|d|ϕ})); auto.
  - rewrite closed_rty_destruct_arrarr in H; mydestr.
    simpl.
    rewrite closed_rty_destruct_arrarr. split; auto.
Qed.

Lemma closed_rty_oarr_implies_closed_rty_retty: forall τ b n d ϕ (L:aset) (c: constant),
    closed_rty 0 L (-:{v: b | n | d | ϕ}⤑ τ) -> closed_rty 0 L ({0 ~r> c} τ).
Proof.
  intros. rewrite closed_rty_destruct_oarr in H; mydestr.
  apply closed_rty_1_open_eq_0; auto.
Qed.

Global Hint Resolve closed_rty_oarr_implies_closed_rty_retty: core.

Lemma ctx_closed_rty_last: forall (L: aset) Γ x τ_x,
    ctx_closed_rty L (Γ ++ [(x, τ_x)]) -> closed_rty 0 (ctxdom ⦑Γ⦒ ∪ L) τ_x.
Proof.
  intros. unfold ctx_closed_rty in H.
  assert (Γ ++ [(x, τ_x)] = Γ ++ [(x, τ_x)] ++ []) as Hz by listctx_set_simpl; eauto.
Qed.

Global Hint Resolve ctx_closed_rty_last: core.

Lemma closed_rty_subst_var: forall a (c_x: constant) m (L: aset) (v: value) τ_x,
    ((exists (n: constant), v = n) \/ (exists (y: atom), v = y)) ->
    closed_rty m L (τ_x ^r^ v) ->
    closed_rty m L (τ_x ^r^ c_x) ->
    closed_rty m L (τ_x ^r^ ({a := c_x }v v)).
Proof.
  intros. destruct H; mydestr; subst; auto.
  destruct (decide (a = x)); subst; auto.
  simpl. dec_solver2. simpl. dec_solver2.
Qed.

Lemma arr_type_in_tyctx_is_free: forall a Γ r (v: value) (b: base_ty),
    is_arr r -> ((a, ⌊r⌋) :: Γ) ⊢t v ⋮v b -> a # v.
Proof.
  intros. destruct v; invclear H0; auto.
  - set_solver.
  - destruct (decide (a = atom)); subst; try fast_set_solver.
    simpl in H4. rewrite decide_True in H4; auto.
    destruct r; invclear H4; try auto_ty_exfalso.
Qed.

Lemma rR_mk_eq_constant: forall c, ({0;b∅;∅}⟦mk_eq_constant c⟧) c.
Proof.
  unfold mk_eq_constant. intros. simpl.
  constructor; auto. constructor; auto.
  - repeat (constructor; auto). fast_set_solver.
  - intros; subst; auto.
Qed.

Global Hint Resolve rR_mk_eq_constant: core.

Lemma rR_mk_under_bot_terr: forall b, ({0;b∅;∅}⟦mk_under_bot b⟧) terr.
Proof.
  unfold mk_under_bot. intros. simpl.
  constructor; auto. constructor; auto.
  - repeat (constructor; auto). fast_set_solver.
  - intros; subst; auto. invclear H0.
Qed.

Global Hint Resolve rR_mk_under_bot_terr: core.

Lemma rR_mk_eq_constant_bool: forall st (b: bool) (v: value),
  ({0;b∅;st}⟦mk_eq_constant b⟧) v -> v = b.
Proof.
  intros. simpl in H; mydestr.
  assert ([] ⊢t b ⋮v TBool). constructor; auto.
  apply H1 in H2; auto. reduction_simpl1. auto.
Qed.

Lemma rR_letapp_arr_lam:
  forall st τ_x e1 (v2: value) τ2,
    is_arr τ2 ->
    ({0;b∅;st}⟦τ2⟧) v2 ->
    ({0;b∅;st}⟦τ2 ⤑ τ_x⟧) (vlam ⌊ τ2 ⌋ e1) ->
    ({0;b∅;st}⟦ τ_x ⟧) (e1 ^t^ v2).
Proof.
  intros; subst. simpl in H0; simpl in H1; mydestr. reduction_simpl0.
  rewrite closed_rty_destruct_arrarr in H2; mydestr. auto_under v2.
  eapply termR_perserve_rR; eauto. refinement_solver.
  apply mk_app_reduce_to_open; refinement_solver.
Qed.

Lemma rR_letapp_arr_fix:
  forall st τ_x e1 (v2: value) τ2,
    is_arr τ2 ->
    ({0;b∅;st}⟦τ2⟧) v2 ->
  ({0;b∅;st}⟦τ2 ⤑ τ_x⟧) (vfix (⌊ τ2 ⌋ ⤍ ⌊ τ_x ⌋ ) (vlam ⌊ τ2 ⌋ e1)) ->
  ({0;b∅;st}⟦ τ_x ⟧) (({1 ~t> v2} e1) ^t^ (vfix (⌊ τ2 ⌋ ⤍ ⌊ τ_x ⌋ ) (vlam ⌊ τ2 ⌋ e1))).
Proof.
  intros; subst. simpl in H0; simpl in H1; mydestr. reduction_simpl0.
  rewrite closed_rty_destruct_arrarr in H2; mydestr. auto_under v2.
  eapply termR_perserve_rR; eauto. refinement_solver.
  apply mk_app_reduce_to_open_fix; refinement_solver.
Qed.

Lemma well_founded_phi_implies_lt: forall st (c c': constant) (ϕ: refinement),
    ϕ b∅ st c -> (≻≻ ϕ) (<b[↦c]> b∅) st c' -> c ≻ c'.
Proof.
  unfold well_founded_constraint. intros. mydestr. auto.
Qed.

Lemma well_founded_phi_implies_phi: forall st bst (c: constant) (ϕ: refinement),
    (≻≻ ϕ) bst st c -> ϕ bst st c.
Proof.
  unfold well_founded_constraint. intros. mydestr. auto.
Qed.

Lemma closed_obase_implies_all_bst: forall b n d ϕ (L: aset),
    closed_rty 0 L {v:b|n|d|ϕ} -> (forall st bst1 bst2 c, ϕ bst1 st c <-> ϕ bst2 st c).
Proof.
  intros. apply bound_in_refinement_0. refinement_solver. invclear H0. invclear H5. auto.
Qed.

Lemma closed_rty_implies_bound_plus1: forall τ m (L:aset),
    closed_rty m L τ -> closed_rty (S m) L τ.
Proof.
  induction τ; intros; auto.
  - invclear H; constructor; auto. invclear H1. constructor; auto.
  - invclear H; constructor; auto. invclear H1. constructor; auto.
  - auto_dclosed_rty. invclear H; constructor; auto. invclear H3. constructor; auto.
  - auto_dclosed_rty.
Qed.

Global Hint Resolve closed_rty_implies_bound_plus1: core.

Lemma rR_implies_bound_plus1: forall τ m bst st e,
    ({m;bst;st}⟦τ⟧) e <-> ({S m;bst;st}⟦τ⟧ e /\ closed_rty m (dom aset st) τ).
Proof.
  induction τ; split; intros; auto; simpl in H; mydestr; subst.
  - do 3 (constructor; eauto).
  - constructor; eauto.
  - do 3 (constructor; eauto).
  - constructor; eauto.
  - do 3 (constructor; eauto). eexists; split; eauto. intros.
    apply H2 in H4; auto. rewrite IHτ in H4; mydestr; auto.
  - do 2 (constructor; eauto). eexists; split; eauto. intros.
    apply H3 in H5; auto. auto_dclosed_rty. rewrite IHτ; split; auto.
  - do 3 (constructor; eauto). eexists; split; eauto. intros.
    auto_dclosed_rty.
    assert (({S m;bst;st}⟦τ1⟧) v_x /\ closed_rty m (dom aset st) τ1) as Hz by auto.
    rewrite <- IHτ1 in Hz. auto_under v_x. rewrite IHτ2 in H2; mydestr; auto.
  - do 2 (constructor; eauto). eexists; split; eauto. intros.
    auto_dclosed_rty. rewrite IHτ1 in H4. mydestr. auto_under v_x.
    rewrite IHτ2. split; auto.
Qed.

Lemma state_subst_implies_rty_subst_rR_all_vc
  : ∀ τ (a: atom) m st bst (c_x : constant) (k : nat) e,
    (closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> c_x} τ) /\
       {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> a} τ⟧ e) <->
    (closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> a} τ) /\
       {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> c_x} τ ⟧ e).
Proof.
  induction τ; split; intros; mydestr.
  - simpl in H0; mydestr. constructor; auto. constructor; auto.
    split; auto.
    eexists; do 2 (split; eauto).
  - simpl in H0; mydestr. constructor; auto. constructor; auto.
    split; auto.
    eexists; do 2 (split; eauto).
  - simpl in H0; mydestr. constructor; auto. constructor; auto.
  - simpl in H0; mydestr. constructor; auto. constructor; auto.
  - simpl in H0; mydestr. constructor; auto. constructor; auto. inv_rd_simpl0.
    constructor; auto.
    eexists; split; eauto. intros.
    simpl in H. rewrite closed_rty_destruct_oarr in H; mydestr.
    apply IHτ; auto.
  - simpl in H0; mydestr. constructor; auto. constructor; auto. inv_rd_simpl0.
    constructor; auto.
    eexists; split; eauto. intros.
    simpl in H. rewrite closed_rty_destruct_oarr in H; mydestr.
    apply IHτ; auto.
  - simpl in H0; mydestr. constructor; auto. constructor; auto. inv_rd_simpl0.
    constructor; auto.
    eexists; split; eauto. intros.
    simpl in H. rewrite closed_rty_destruct_arrarr in H; mydestr.
    rewrite closed_rty_destruct_arrarr in H1; mydestr.
    apply IHτ2; eauto. split; auto.
    apply H3; auto. apply IHτ1; auto.
  - simpl in H0; mydestr. constructor; auto. constructor; auto. inv_rd_simpl0.
    constructor; auto.
    eexists; split; eauto. intros.
    simpl in H. rewrite closed_rty_destruct_arrarr in H; mydestr.
    rewrite closed_rty_destruct_arrarr in H1; mydestr.
    apply IHτ2; eauto. split; auto.
    apply H3; auto. apply IHτ1; auto.
Qed.

Lemma state_subst_implies_rty_subst_rR_all_v_to_c
  : ∀ τ (a: atom) m st bst (c_x : constant) (k : nat) e,
    closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> c_x} τ) ->
    {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> a} τ⟧ e ->
    {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> c_x} τ ⟧ e.
Proof.
  intros. assert (closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> c_x} τ) /\
       {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> a} τ⟧ e); auto.
  rewrite state_subst_implies_rty_subst_rR_all_vc in H1; mydestr; auto.
Qed.

Lemma state_subst_implies_rty_subst_rR_all_c_to_v
  : ∀ τ (a: atom) m st bst (c_x : constant) (k : nat) e,
    closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> a} τ) ->
    {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> c_x} τ⟧ e ->
    {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> a} τ ⟧ e.
Proof.
  intros. assert (closed_rty m (dom aset (<[a:=c_x]> st)) ({k ~r> a} τ) /\
       {m;bst;(<[a:=c_x]> st)}⟦ {k ~r> c_x} τ⟧ e); auto.
  rewrite <- state_subst_implies_rty_subst_rR_all_vc in H1; mydestr; auto.
Qed.

Lemma unfold_rty_obase: forall B n d ϕ k v,
    {v:B|n `min` k|refinement_set_open k v d|refinement_open k v ϕ} =
      {k ~r> v} {v:B|n|d|ϕ}.
Proof.
  intros; auto.
Qed.

Lemma unfold_rty_ubase: forall B n d ϕ k v,
    [v:B|n `min` k|refinement_set_open k v d|refinement_open k v ϕ] =
      {k ~r> v} [v:B|n|d|ϕ].
Proof.
  intros; auto.
Qed.

From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.

Lemma wf_implies_base_phi_sat: forall m bst st b1 n1 d1 ϕ1 (c2: constant),
  (∀ e_wf : tm, ({m;bst;st}⟦[v:b1|n1|d1|ϕ1]⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) ->
  ({m;bst;st}⟦[v:b1|n1|d1|ϕ1]⟧) c2 -> ϕ1 bst st c2 /\ [] ⊢t c2 ⋮v b1.
Proof.
  intros. invclear H0; mydestr.
  destruct (classic (exists c: constant, ϕ1 bst st c /\ [] ⊢t c ⋮v b1)).
  - mydestr. assert (c2 ↪* x); auto. reduction_simpl1; subst. invclear H5; auto.
  - neg_simpl. assert ({m;bst;st}⟦[v:b1|n1|d1|ϕ1]⟧ terr).
    do 2 constructor; auto. intros. apply H3 in H5. exfalso. apply H5; auto.
    apply H in H4. mydestr. auto_reduction_exfalso1.
Qed.

Lemma rR_letapp_overbase_underbase:
  forall st τ_x (v1: value) (c2: constant) b1 n1 d1 ϕ1 b2 n2 d2 ϕ2,
  τ_x = [v:b2|n2|d2|ϕ2] ->
  (∀ e_wf : tm, ({0;b∅;st}⟦[v:b1|n1|d1|ϕ1]⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) ->
  ({0;b∅;st}⟦[v:b1|n1|d1|ϕ1]⟧) c2 ->
  ({0;b∅;st}⟦-:{v:b1|n1|d1|ϕ1}⤑ τ_x⟧) v1 ->
  (exists e1, ({0;b∅;st}⟦ τ_x ^r^ c2 ⟧) e1 /\ e1 <-<{ []; b2} (mk_app v1 c2)).
Proof.
  intros; subst.
  assert (ϕ1 b∅ st c2 /\ [] ⊢t c2 ⋮v b1) as (Hz & HzT). eapply wf_implies_base_phi_sat; eauto.
  destruct (rR_arrow_value_lam_exists_oarr _ _ _ _ _ _ _ _ _ H2); mydestr; subst.
  - rename x into e1. exists (e1 ^t^ c2). split.
    + invclear H2; invclear H1; mydestr. reduction_simpl0.
      apply H6 in Hz; auto.
      apply rR_open_trans_empty' in Hz; auto.
      eapply termR_perserve_rR; eauto. refinement_solver. simpl.
      apply mk_app_reduce_to_open; auto. basic_typing_solver.
    + apply mk_app_reduce_to_open'; auto. refinement_solver.
  - rename x into e1. exists (({1 ~t> c2} e1) ^t^ (vfix (b1 ⤍ b2) (vlam b1 e1))). split.
    + invclear H2; invclear H1; mydestr. reduction_simpl0. apply H6 in Hz; auto.
      apply rR_open_trans_empty' in Hz; auto.
      eapply termR_perserve_rR; eauto. refinement_solver. simpl.
      apply mk_app_reduce_to_open_fix; auto. refinement_solver.
    + apply mk_app_reduce_to_open_fix'; auto. refinement_solver.
Qed.

Lemma rR_letapp_overbase_lam:
  forall st τ_x e1 (c2: constant) b1 n1 d1 ϕ1,
  (∀ e_wf : tm, ({0;b∅;st}⟦[v:b1|n1|d1|ϕ1]⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) ->
  ({0;b∅;st}⟦[v:b1|n1|d1|ϕ1]⟧) c2 ->
  ({0;b∅;st}⟦-:{v:b1|n1|d1|ϕ1}⤑ τ_x⟧) (vlam b1 e1) ->
  ({0;b∅;st}⟦ τ_x ^r^ c2 ⟧) (e1 ^t^ c2).
Proof.
  intros; subst.
  assert (ϕ1 b∅ st c2 /\ [] ⊢t c2 ⋮v b1) as (Hz & HzT). eapply wf_implies_base_phi_sat; eauto.
  invclear H0; invclear H1; mydestr. reduction_simpl0. apply H6 in Hz; auto.
  apply rR_open_trans_empty' in Hz; auto.
  eapply termR_perserve_rR; eauto. refinement_solver. refinement_solver.
  apply mk_app_reduce_to_open; auto.
  inv_rd_simpl3. inv_rd_simpl0.
Qed.

Lemma rR_letapp_overbase_fix:
  forall st τ_x e1 (c2: constant) b1 n1 d1 ϕ1,
  (∀ e_wf : tm, ({0;b∅;st}⟦[v:b1|n1|d1|ϕ1]⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) ->
  ({0;b∅;st}⟦[v:b1|n1|d1|ϕ1]⟧) c2 ->
  ({0;b∅;st}⟦-:{v:b1|n1|d1|ϕ1}⤑ τ_x⟧) (vfix (b1 ⤍ ⌊ τ_x ⌋ ) (vlam b1 e1)) ->
  ({0;b∅;st}⟦ τ_x ^r^ c2 ⟧) (({1 ~t> c2} e1) ^t^ (vfix (b1 ⤍ ⌊ τ_x ⌋) (vlam b1 e1))).
Proof.
  intros; subst.
  assert (ϕ1 b∅ st c2 /\ [] ⊢t c2 ⋮v b1) as (Hz & HzT). eapply wf_implies_base_phi_sat; eauto.
  invclear H0; invclear H1; mydestr. reduction_simpl0. apply H6 in Hz; auto.
  apply rR_open_trans_empty' in Hz; auto.
  eapply termR_perserve_rR; eauto. refinement_solver. refinement_solver.
  inv_rd_simpl0.
  apply mk_app_reduce_to_open_fix; auto.
Qed.

Lemma wf_implies_base_phi_sat_v: forall m bst st b1 n1 d1 ϕ1 (v2: value),
  (∀ e_wf : tm, ({m;bst;st}⟦[v:b1|n1|d1|ϕ1]⟧) e_wf → ∃ v_wf : value, e_wf ↪* v_wf) ->
  ({m;bst;st}⟦[v:b1|n1|d1|ϕ1]⟧) v2 ->
  (exists c2: constant, v2 = c2 /\ ϕ1 bst st c2 /\ [] ⊢t c2 ⋮v b1).
Proof.
  intros. assert (exists c2: constant, v2 = c2) by eauto. mydestr; subst.
  eapply wf_implies_base_phi_sat in H0; eauto.
Qed.
