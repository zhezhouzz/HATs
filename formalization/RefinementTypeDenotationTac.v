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
From CT Require Import TermOrdering.
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
Import TermOrdering.

Lemma refinement_exclude_const: forall b (ϕ: refinement),
    (∀ c: constant, [] ⊢t c ⋮v b → ~ ϕ b∅ ∅ c) \/ (exists c: constant, [] ⊢t c ⋮v b /\ ϕ b∅ ∅ c).
Proof.
  intros.
  destruct (classic (exists c: constant, [] ⊢t c ⋮v b /\ ϕ b∅ ∅ c)); auto.
  - left. intros. intro Hf. apply H. exists c. split; auto.
Qed.

Lemma terr_reduction_iff_false_phi: forall bst st b (ϕ: refinement),
    (∀ c : constant, [] ⊢t c ⋮v b → ϕ bst st c → terr ↪* c) <-> (forall c: constant, [] ⊢t c ⋮v b → ~ ϕ bst st c).
Proof.
  split; intros.
  - intros Hf. apply H in Hf; auto. auto_reduction_exfalso.
  - apply H in H0. auto_reduction_exfalso.
Qed.

Lemma terr_inhabitant_iff_false_phi: forall n1 n2 bst st (d: aset) b (ϕ: refinement),
    {n1; bst; st}⟦ [v: b | n2 | d | ϕ ] ⟧ terr <->
      (closed_rty n1 (dom aset st) [v:b|n2|d|ϕ] /\ forall c: constant, [] ⊢t c ⋮v b → ~ ϕ bst st c).
Proof.
  split; intros.
  - invclear H. mydestr; subst. rewrite terr_reduction_iff_false_phi in H1; auto.
  - mydestr. constructor; auto. split; auto. rewrite terr_reduction_iff_false_phi; auto.
Qed.

Definition base_type_max_term (b: base_ty) :=
  match b with
  | TNat => nat-gen
  | TBool => bool-gen
  end.

Ltac denotation_simp0 :=
  my_simplify_map_eq3;
  ctx_erase_simp;
  repeat match goal with
    | [H: forall bst, ({0;bst; _ }⟦ _ ⟧) _ |- _ ] => specialize (H b∅); invclear H; mydestr
    | [H: _ ⊢t (tvalue ?v) ⋮t _ |- _ ] => invclear H
    | [H: _ ⊢t _ ⋮t ⌊ _ ⌋ |- _ ] => progress simpl in H
    | [H: _ ⊢t _ ⋮v ⌊ _ ⌋ |- _ ] => progress simpl in H
    | [H: _ ⊢t ?v ⋮v (TBase _) |- _ ] =>
        match v with
        | vconst _ => fail 1
        | _ => set H as Htmp; apply empty_basic_typing_base_const_exists in Htmp; mydestr; subst
        end
    | [H: ∀ c, [] ⊢t (vconst c) ⋮v _ → _ _ ∅ c → terr ↪* (tvalue (vconst c)) |- _ ] =>
        rewrite terr_reduction_iff_false_phi in H
    end.

Lemma base_type_max_term_typable: forall b, [] ⊢t base_type_max_term b ⋮t b.
Proof.
  destruct b; simpl; eauto.
Qed.

Global Hint Resolve base_type_max_term_typable: core.

Lemma base_type_max_term_spec: forall (b: base_ty) (c: constant), [] ⊢t c ⋮v b -> base_type_max_term b ↪* c.
Proof.
  destruct b; simpl; intros; eauto; destruct c; invclear H; subst; eauto.
Qed.

Global Hint Resolve base_type_max_term_spec: core.

Lemma base_type_reduce_to_constant: forall e (b: base_ty) (v: value), [] ⊢t e ⋮t b -> e ↪* v -> (∃ c, v = vconst c).
Proof.
  intros.
  eapply multi_preservation in H; eauto. denotation_simp0. eapply empty_basic_typing_base_const_exists; eauto.
Qed.

Lemma base_type_max_term_reduce_to_constant: forall b (v: value), base_type_max_term b ↪* v -> (∃ c, v = vconst c).
Proof.
  intros. assert ([] ⊢t base_type_max_term b ⋮t b); eauto.
  eapply multi_preservation in H; eauto. denotation_simp0. eapply empty_basic_typing_base_const_exists; eauto.
Qed.

Global Hint Resolve base_type_max_term_reduce_to_constant: core.

Lemma state_insert_closed_value:
  forall (v: value) a (st: state), closed_value v -> (exists (c: constant), v = c) \/ ({a↦v} st = st).
Proof.
  unfold closed_value. intros. destruct v; simpl in H.
  - left. eauto.
  - set_solver.
  - right; eauto.
  - right; eauto.
  - right; eauto.
Qed.

Lemma state_insert_closed_value_arr: forall (r: rty) (v : value) (a : atom) (st : state),
    is_arr r -> [] ⊢t v ⋮v ⌊ r ⌋ -> ({a↦v}) st = st.
Proof.
  intros.
  assert (closed_value v); basic_typing_solver.
  eapply state_insert_closed_value in H1; destruct H1; eauto.
  mydestr; subst. destruct r; invclear H0. invclear H. invclear H.
Qed.

Lemma ctx_rm_app: forall Γ1 Γ2, ⦑Γ1 ++ Γ2⦒ = ⦑Γ1⦒ ++ ⦑Γ2⦒.
Proof.
  induction Γ1; simpl; intros; mydestr; auto.
  dec_solver2. rewrite IHΓ1; auto.
Qed.

Ltac denotation_simp1 :=
  repeat (denotation_simp0;
          mydestr;
          repeat match goal with
            | [H: ¬ is_arr _ |- _ ] => apply not_is_arr in H; destruct H; mydestr; subst
            | [H: ¬ not_underbasety _ |- _ ] => apply not_not_underbasety in H; mydestr; subst
            | [H: closed_rty 0 _ [v:_|?n|_|_] |- _ ] =>
                match n with
                | 0 => fail 1
                | _ => assert (n = 0) by (apply closed_rty_0_underbase in H; auto); subst
                end
            | [H: closed_rty 0 _ {v:_|?n|_|_} |- _ ] =>
                match n with
                | 0 => fail 1
                | _ => assert (n = 0) by (apply closed_rty_0_overbase in H; auto); subst
                end
            | [H: ?e ↪* (tvalue ?v), H': [] ⊢t ?e ⋮t (TBase _)  |- _ ] =>
                match v with
                | vconst _ => fail 1
                | _ => assert (exists c, v = vconst c) as Htmp by (eapply base_type_reduce_to_constant in H; eauto);
                      destruct Htmp; subst
                end
            | [H: base_type_max_term _ ↪* (tvalue ?v) |- _ ] =>
                match v with
                | vconst _ => fail 1
                | _ => assert (exists c, v = vconst c) as Htmp by (eapply base_type_max_term_reduce_to_constant in H; eauto);
                      destruct Htmp; subst
                end
            | [H: context [⦑(_, _) :: _⦒] |- _ ] => simpl in H; try dec_solver2
            | [|- context [⦑(_, _) :: _⦒] ] => simpl; try dec_solver2
            | [H: context [⦑ ?a ++ ?b ⦒] |- _ ] => setoid_rewrite (ctx_rm_app a b) in H
            | [|- context [⦑ ?a ++ ?b ⦒] ] => setoid_rewrite (ctx_rm_app a b)
            | [H: context [ctxdom ((_, _) :: _)] |- _] => simpl in H
            | [|- context [ctxdom ((_, _) :: _)]] => simpl
            | [H: is_arr ?r, H': [] ⊢t ?v ⋮v ⌊ ?r ⌋ |- context [{ ?a ↦ ?v} _] ] =>
                rewrite (state_insert_closed_value_arr r v a); auto
            | [H: is_arr ?r, H': [] ⊢t ?v ⋮v ⌊ ?r ⌋, H'': context [{ ?a ↦ ?v} _] |- _ ] =>
                rewrite (state_insert_closed_value_arr r v a) in H''; auto
            | [H: tvalue ?a = tvalue ?b |- _ ] => invclear H
            | [H: vconst ?a = vconst ?b |- _ ] => invclear H
            | [H: ty_of_const ?a = ty_of_const ?b |- _ ] => invclear H
            | [H: context [⌊(_, _) :: _⌋*] |- _ ] => simpl in H
            | [|- context [⌊(_, _) :: _⌋*]] => simpl
            end).

Lemma valid_rty_under_iff_over: forall n b (d2: aset) (ϕ: refinement),
    valid_rty {v:b|n|d2|ϕ} <-> valid_rty [v:b|n|d2|ϕ].
Proof.
  split; intros; invclear H; constructor; auto.
Qed.

Global Hint Rewrite valid_rty_under_iff_over: core.

Lemma closed_rty_under_iff_over: forall n1 n2 b (d1 d2: aset) (ϕ: refinement),
    closed_rty n1 d1 {v:b|n2|d2|ϕ} <-> closed_rty n1 d1 [v:b|n2|d2|ϕ].
Proof.
  split; intros; invclear H; constructor; auto.
  - rewrite <- valid_rty_under_iff_over; auto.
  - invclear H1; constructor; auto.
  - rewrite valid_rty_under_iff_over; auto.
  - invclear H1; constructor; auto.
Qed.

Lemma rR_perservation: forall st r e e', ({st}⟦r⟧) e -> e ↪* e' -> [] ⊢t e' ⋮t ⌊r⌋.
Proof.
  intros. apply rR_regular1 in H; mydestr. eapply multi_preservation in H0; eauto.
Qed.

Lemma closed_rty_destruct_oarr: forall τ m L b n d ϕ,
  closed_rty m L (-:{v: b | n | d | ϕ}⤑ τ) <->
    (closed_rty m L {v: b | n | d | ϕ} /\ closed_rty (S m) L τ /\ not_overbasety τ).
Proof.
  repeat split; intros; invclear H; mydestr; auto.
  - invclear H0; auto. constructor; auto.
  - invclear H1; auto. constructor; auto.
  - set_solver.
  - invclear H0; auto.
  - invclear H1; auto.
  - set_solver.
  - invclear H0; auto.
  - invclear H; invclear H0; auto. constructor; auto. invclear H; auto.
  - invclear H; invclear H0; auto. constructor; auto. invclear H5; auto.
  - invclear H; invclear H0; auto. set_solver.
Qed.

Lemma closed_rty_destruct_arrarr: forall m L τ1 τ2,
  closed_rty m L (τ1 ⤑ τ2) <->
    (closed_rty m L τ1 /\ closed_rty m L τ2 /\ is_arr τ1 /\ not_overbasety τ2).
Proof.
    repeat split; intros; invclear H; mydestr; auto.
  - invclear H0; auto.
  - invclear H1; auto.
  - set_solver.
  - invclear H0; auto.
  - invclear H1; auto.
  - set_solver.
  - invclear H0; simpl; auto.
  - invclear H0; auto.
  - invclear H; invclear H0; auto. destruct τ1; invclear H1; constructor; auto.
  - invclear H; invclear H0; auto. constructor; auto.
  - invclear H; invclear H0; auto. set_solver.
Qed.

Ltac auto_dclosed_rty:=
  repeat match goal with
    | [H: closed_rty _ _ (-:{v: _ | _ | _ | _}⤑ _) |- _ ] => rewrite closed_rty_destruct_oarr in H; mydestr; auto
    | [H: closed_rty _ _ (_ ⤑ _) |- _ ] => rewrite closed_rty_destruct_arrarr in H; mydestr; auto
    | [|- closed_rty _ _ (-:{v: _ | _ | _ | _}⤑ _) ] => rewrite closed_rty_destruct_oarr; split; auto
    | [|- closed_rty _ _ (_ ⤑ _)] => rewrite closed_rty_destruct_arrarr; mydestr; split; auto
    end.

Ltac valid_solver :=
  repeat match goal with
    | [H: valid_rty (-:{v: _ | _ | _ | _}⤑ ?τ) |- valid_rty ?τ] => invclear H; auto
    | [H: valid_rty (-:{v: ?b | ?n | ?d | ?ϕ}⤑ _) |- valid_rty {v: ?b | ?n | ?d | ?ϕ}] => invclear H; auto
    | [H: valid_rty (_ ⤑ ?τ) |- valid_rty ?τ] => invclear H; auto
    | [H: valid_rty (?τ ⤑ _) |- valid_rty ?τ] => invclear H; auto
    | [H: valid_rty (-:{v: _ | _ | _ | ?ϕ}⤑ _) |- not_fv_in_refinement _ ?ϕ] => invclear H
    | [H: wf_r _ _ ?ϕ |- not_fv_in_refinement _ ?ϕ] => invclear H; auto
    end.

Ltac refinement_solver0 :=
  repeat (auto_dclosed_rty;
          valid_solver;
          ((match goal with
            | [H: {_;_;_}⟦_⟧ ?e |- lc ?e] => apply rR_regular1 in H; mydestr; basic_typing_solver2
            | [H: ({0;b∅;_}⟦?r⟧) ?x, H': ?x ↪* ?y |- [] ⊢t ?y ⋮t ⌊?r⌋ ] =>
                apply (rR_perservation _ r x y) in H; auto
            | [H: ({0;b∅;_}⟦?r⟧) ?x, H': ?x ↪* (tvalue ?y) |- [] ⊢t ?y ⋮v ⌊?r⌋ ] =>
                (apply (rR_perservation _ r x y) in H; auto); (invclear H; auto)
            | [H: closed_rty _ _ _ |- bound_in_refinement _ _ ] => destruct H; mydestr
            | [H: valid_rty _ |- bound_in_refinement _ _ ] => invclear H
            | [H: valid_rty ?τ |- wf_r _ _ ?ϕ ] =>
                match τ with
                | context [ ϕ ] => invclear H; eauto
                end
            | [H: closed_rty _ _ ?τ |- wf_r _ _ ?ϕ ] =>
                match τ with
                | context [ ϕ ] => invclear H; mydestr; eauto
                end
            | [H: wf_r _ _ ?ϕ |- bound_in_refinement _ ?ϕ ] => destruct H
            | [H: ({_;_;_}⟦?τ⟧) _ |- closed_rty _ _ ?τ ] =>
                apply rR_regular1 in H; mydestr; eauto; try closed_rty_solver
            | [H: ({_;_;_}⟦?τ⟧) _ |- _ ⊢t _ ⋮t _ ] =>
                apply rR_regular1 in H; mydestr; eauto; try basic_typing_solver
            | [ |- closed_rty _ _ _ ] => closed_rty_solver
            | [H: ok_dctx _ _ |- ok _ ] => ok_dctx_solver
            | [ |- ok ((_, _) :: _)] => rewrite ok_pre_destruct; split; ctx_erase_simp
            | [H: closed_rty _ _ ?τ |- _ ∉ rty_fv ?τ ] => invclear H; mydestr; try fast_set_solver
            end; refinement_simp1; eauto) || (listctx_set_solver; fast_set_solver))).

Global Hint Constructors lc_rty_idx: core.

Ltac dec_solver3 :=
  try auto_exfalso;
  match goal with
  | [H: Some ?a = Some ?b |- _] => inversion H; subst; clear H; simpl; auto
  | [H: ?a <> ?a |- _ ] => exfalso; lia
  | [ |- Some _ = None ] => exfalso; lia
  | [ |- None = Some _ ] => exfalso; lia
  | [H: context [ decide (?a ∈ ?d) ] |- _ ] => destruct (decide (a ∈ d)); subst; my_simplify_map_eq; eauto
  | [|- context [ decide (?a ∈ ?d) ] ] => destruct (decide (a ∈ d)); subst; my_simplify_map_eq; eauto
  | [H: context [ decide (?a = ?b) ] |- _ ] =>
      (assert (a = b) as Htmp by lia; rewrite (decide_True _ _ Htmp) in H; try clear Htmp) ||
        (assert (a <> b) as Htmp by lia; rewrite (decide_False _ _ Htmp) in H; try clear Htmp)
  | _ => progress (intros; simpl; eauto; dec_solver2; var_dec_solver2)
  end.

Lemma rty_fv_subst_excluded_forward: forall τ (z: atom) (c: constant) d1,
    rty_fv τ ⊆ {[z]} ∪ d1 -> rty_fv (({z:=c}r) τ) ⊆ d1.
Proof.
  induction τ; simpl; intros; unfold refinement_set_subst.
  - dec_solver3; set_solver.
  - dec_solver3; set_solver.
  - dec_solver3; set_solver.
  - set_solver.
Qed.

Lemma wf_r_subst_excluded_forward_c: forall n d ϕ z (c: constant),
    wf_r n d ϕ -> wf_r n (refinement_set_subst z c d) (refinement_subst z c d ϕ).
Proof.
  intros. invclear H. unfold refinement_subst. unfold refinement_set_subst.
  dec_solver3; constructor; auto.
  - unfold not_fv_in_refinement. intros. apply H0. intros.
    unfold state_subst. dec_solver3.
    destruct (atom_dec x z); subst; my_simplify_map_eq3.
  - unfold bound_in_refinement in H1. unfold bound_in_refinement. intros. dec_solver3.
  - unfold not_fv_in_refinement. intros. apply H0. intros.
    unfold state_subst. var_dec_solver2.
  - unfold bound_in_refinement in H1. unfold bound_in_refinement. intros. dec_solver3.
Qed.

Lemma wf_r_subst_excluded_forward: forall n d ϕ z (c: value),
    wf_r n d ϕ -> wf_r n (refinement_set_subst z c d) (refinement_subst z c d ϕ).
Proof.
  intros. invclear H. unfold refinement_subst. unfold refinement_set_subst.
  dec_solver3; constructor; auto.
  - destruct c; auto; unfold not_fv_in_refinement; intros; apply H0; intros;
      unfold state_subst; dec_solver3.
    + destruct (atom_dec x z); subst; my_simplify_map_eq3.
    + unfold state_subst_var. destruct (decide (z = atom)).
      { assert (m !! atom = m' !! atom) by fast_set_solver. rewrite <- H3. dec_solver2.
        destruct (m!!atom);
          destruct (atom_dec x atom); subst; my_simplify_map_eq3.
      }
      { assert (m !! atom = m' !! atom) by fast_set_solver. rewrite <- H3. dec_solver2.
        destruct (m!!atom); my_simplify_map_eq3;
          destruct (atom_dec z x); subst; my_simplify_map_eq3. }
  - unfold bound_in_refinement in H1. unfold bound_in_refinement. intros. dec_solver3.
  - unfold not_fv_in_refinement. intros. apply H0. intros.
    unfold state_subst. var_dec_solver2.
  - unfold bound_in_refinement in H1. unfold bound_in_refinement. intros. dec_solver3.
Qed.

Lemma not_overbasety_subst_excluded_forward: forall τ z c,
    not_overbasety τ -> not_overbasety (({z:=c}r) τ).
Proof.
  induction τ; intros; auto.
Qed.

Lemma valid_rty_subst_excluded_forward: forall τ (z: atom) (c: value),
    valid_rty τ -> valid_rty (({z:=c}r) τ).
Proof.
  induction τ; intros.
  - constructor. invclear H. apply wf_r_subst_excluded_forward; auto.
  - constructor. invclear H. apply wf_r_subst_excluded_forward; auto.
  - invclear H. simpl. constructor; eauto.
    + apply wf_r_subst_excluded_forward; auto.
    + apply not_overbasety_subst_excluded_forward; auto.
  - simpl. invclear H. simpl. constructor; eauto.
    + apply not_overbasety_subst_excluded_forward; auto.
    + simpl. constructor; eauto. apply not_overbasety_subst_excluded_forward; auto.
Qed.

Lemma lc_rty_idx_subst_excluded_forward: forall τ (z: atom) (c: value) n1,
    lc_rty_idx n1 τ -> lc_rty_idx n1 (({z:=c}r) τ).
Proof.
  induction τ; intros; invclear H; constructor; auto.
Qed.

Lemma closed_rty_subst_excluded_forward: forall τ (z: atom) (c: constant) n1 (d1: aset),
    z ∉ d1 -> closed_rty n1 ({[z]} ∪ d1) τ -> closed_rty n1 d1 ({z := c}r τ).
Proof.
  induction τ; intros; repeat split; invclear H0; mydestr;
    try match goal with
      | [|- valid_rty _] => eapply valid_rty_subst_excluded_forward; eauto
      | [|- lc_rty_idx _ _] => eapply lc_rty_idx_subst_excluded_forward; eauto
      | [|- rty_fv _ ⊆ _] => eapply rty_fv_subst_excluded_forward; eauto
      end.
Qed.

Lemma wf_r_implies_state_dummy_insert: forall n2 d2 ϕ z,
    wf_r n2 d2 ϕ -> z ∉ d2 -> (forall st bst c v, (ϕ bst (<[z:=c]> st) v <-> ϕ bst st v)).
Proof.
  intros. invclear H. apply H1. intros.
  my_simplify_map_eq3.
Qed.

Lemma closed_rty_over_implies_state_dummy_insert: forall n1 d1 n2 d2 B ϕ z,
    closed_rty n1 d1 {v:B|n2|d2|ϕ} -> z ∉ d2 -> (forall st bst c v, (ϕ bst (<[z:=c]> st) v <-> ϕ bst st v)).
Proof.
  intros. eapply wf_r_implies_state_dummy_insert; eauto. refinement_solver0.
Qed.

Lemma closed_rty_under_implies_state_dummy_insert: forall n1 d1 n2 d2 B ϕ z,
    closed_rty n1 d1 [v:B|n2|d2|ϕ] -> z ∉ d2 -> (forall st bst c v, (ϕ bst (<[z:=c]> st) v <-> ϕ bst st v)).
Proof.
  intros. eapply wf_r_implies_state_dummy_insert; eauto. refinement_solver0.
Qed.

Lemma tyable_implies_closed_value: forall v_x T, [] ⊢t v_x ⋮v T -> closed_value v_x.
Proof.
  unfold closed_value. intros. apply basic_typing_contains_fv_value in H.
  set_solver.
Qed.

Global Hint Resolve tyable_implies_closed_value: core.

Lemma tyable_implies_closed_tm: forall v_x T, [] ⊢t v_x ⋮t T -> closed_tm v_x.
Proof.
  unfold closed_tm. intros. apply basic_typing_contains_fv_tm in H.
  set_solver.
Qed.

Global Hint Resolve tyable_implies_closed_tm: core.

Ltac refinement_solver7 :=
  repeat (
      try auto_reduction_exfalso;
      listctx_set_simpl4;
      auto_dclosed_rty;
      match goal with
      | [H: ok_dctx _ ((?a, ?b) :: ?c ++ _) |- ok_dctx _ ((?a, ?b) :: ?c) ] =>
          rewrite app_comm_cons in H;
          rewrite ok_dctx_post_destruct in H; mydestr; auto
      | [H: {0;b∅;?st}⟦?r⟧ (tvalue ?v_x) |- _ ∉ fv_value ?v_x ] =>
          apply rR_regular2 in H; mydestr; basic_typing_solver
      | [H: {0;b∅;?st}⟦?r⟧ (tvalue ?v_x) |- closed_value ?v_x ] =>
          apply rR_regular2 in H; mydestr; basic_typing_solver
      | [H: {0;b∅;?st}⟦?r⟧ (tvalue ?v_x) |- fv_value ?v_x ≡ ∅ ] =>
          apply rR_regular2 in H; mydestr; basic_typing_solver
      | [H: is_arr ?τ_x |- ok_dctx _ ((_, ?τ_x) :: _)] => apply ok_dctx_cons_arr
      | [|- ok_dctx _ ((_, {v:_|_|_|_}) :: _)] => constructor
      | [|- ok_dctx _ ((_, [v:_|_|_|_]) :: _)] => constructor
      | [H: [] ⊢t ?v ⋮v _ |- closed_value ?v] => eapply tyable_implies_closed_value in H; eauto
      | [H: [] ⊢t ?v ⋮t _ |- closed_tm ?v] => eapply tyable_implies_closed_tm in H; eauto
      | [H: ({_;_;_}⟦ ?τ ⟧) _ |- valid_rty ?τ] => apply rR_regular1 in H; mydestr
      | [H: ({_;_;_}⟦?τ⟧) _ |- _ ∉ rty_fv ?τ ] => apply rR_regular1 in H; mydestr
      | [H: ({_;_;_}⟦_⟧ _) |- _ ⊢t ?v ⋮v _ ] => apply rR_regular1 in H; mydestr
      | [H: {_;_;_}⟦_⟧ ?e |- _ ∉ fv_tm ?e] =>
          apply rR_regular1 in H; mydestr; basic_typing_solver
      | [H: closed_rty _ _ _ |- lc_rty_idx _ _] => invclear H; mydestr; auto
      | [H: closed_rty _ _ _ |- context [rty_fv _]] => invclear H; mydestr; auto
      | [|- valid_rty (({ _ := _ }r) _)] => eapply valid_rty_subst_excluded_forward; eauto
      | [|- lc_rty_idx _ (({ _ := _ }r) _)] => eapply lc_rty_idx_subst_excluded_forward; eauto
      | [|- rty_fv (({ _ := _ }r) _) ⊆ _] => eapply rty_fv_subst_excluded_forward; eauto
      | [H: closed_rty _ _ ?τ |- valid_rty ?τ] => destruct H; auto
      | [ |- _ ⊢t terr ⋮t _ ] => constructor; auto
      | [H: ok_dctx ?d ((_, ?τ) :: _) |- closed_rty 0 ?d ?τ ] => invclear H; auto
      | [H: ok_dctx _ _ |- ok _ ] => apply ok_dctx_regular2 in H; mydestr
      | [H: ok (_ :: ?Γ) |- ok ⌊?Γ⌋* ] => rewrite ok_pre_destruct in H; mydestr; ctx_erase_simp
      | [ |- context [ ⌊ _ ⌋* ] ] => ctx_erase_simp; fast_set_solver
      | [H: ?e ↪* (tvalue ?v), H': [] ⊢t ?e ⋮t ?T |- [] ⊢t ?v ⋮v ?T ] =>
          eapply multi_preservation_value in H'; eauto
      | [H: [] ⊢t ?e ⋮t ?T |- _ ⊢t ?e ⋮t _ ] => apply basic_typing_weaken_tm_empty; eauto
      | [H: lc_rty_idx _ _ |- lc_rty_idx _ _ ] => invclear H; auto
      | [H: wf_r _ _ ?ϕ |- not_fv_in_refinement _ ?ϕ ] => invclear H; auto
      | [H: closed_rty _ _ _ |- wf_r _ _ _ ] => invclear H; mydestr; eauto
      | [H: closed_rty _ _ ?τ |- valid_rty ?τ] => invclear H; mydestr; eauto
      | [H: valid_rty _ |- wf_r _ _ _ ] => invclear H; mydestr; eauto
      | [H: ok_dctx _ ((?z, _) :: _) |- ?z ∉ _ ] => invclear H; auto
      | [H: not_overbasety ?τ |- not_overbasety (({ _ := _}r) ?τ)] =>
          eapply not_overbasety_subst_excluded_forward; eauto
      end || refinement_solver0).

Ltac denotation_simp3 :=
  denotation_simp1;
  repeat match goal with
    | [H: ({_}⟦[v:?b|_|_|_]⟧) ?ee, H': ?ee ↪* (tvalue ?v), H'': [] ⊢t ?v ⋮v (TBase ?b) |- _ ] => fail 1
    | [H: ({_}⟦[v:?b|_|_|_]⟧) ?ee, H': ?ee ↪* (tvalue ?v) |- _ ] => assert ([] ⊢t v ⋮v b) by refinement_solver7
    | [H: ({_;_;_}⟦[v:?b|_|_|_]⟧) ?ee, H'': [] ⊢t ?ee ⋮t (TBase ?b) |- _ ] => fail 1
    | [H: ({_;_;_}⟦[v:?b|_|_|_]⟧) ?ee |- _ ] => assert ([] ⊢t ee ⋮t b) by refinement_solver7
    | [H: ok [] |- _ ] => clear H
    | [H: [] ⊢t ?v ⋮v (TBase _) |- _ ] => invclear H; denotation_simp1
    | [H: [v: _ |_|_|_] = [v:_|_|_|_] |- _ ] => invclear H
    end.

Ltac denotation_simp := denotation_simp3.

Ltac refinement_solver :=
  (refinement_solver7; (try denotation_simp; refinement_solver7)).

Ltac dsimp1 :=
  match goal with
  | [H: ({0;b∅;_}⟦[v:?b|_|_|_]⟧) ?e, H': ?e ↪* (tvalue ?v) |- _ ] =>
      assert ([] ⊢t v ⋮v b) by refinement_solver; denotation_simp3
  end.

Lemma rR_eval_op_under_bound_tm: forall st (op: biop) (v1: nat) (v2: nat),
    ({0;b∅;st}⟦[v:ret_ty_of_op op|0|∅|refinement_open 1 v2
                                        (refinement_open 0 v1
                                           (λ (bst : bstate) (_ : state) (v : constant),
                                             eval_op op (bst 0) (bst 1) v))]⟧)
      (eval_op_under_bound_tm op v1 v2).
Proof.
  unfold refinement_open; intros. constructor; simpl; auto.
  do 2 (constructor; auto).
  - do 2 (constructor; auto).
    + unfold not_fv_in_refinement; auto.
    + unfold bound_in_refinement. intros. unfold bstate_insert. dec_solver2.
  - fast_set_solver.
Qed.

Lemma rR_eval_op_under_bound_tm_min: forall st (op: biop) (v1: nat) (v2: nat) e,
    ({0;b∅;st}⟦[v:ret_ty_of_op op|0|∅|refinement_open 1 v2
                                        (refinement_open 0 v1
                                           (λ (bst : bstate) (_ : state) (v : constant),
                                             eval_op op (bst 0) (bst 1) v))]⟧) e ->
    (forall (v_x: value), eval_op_under_bound_tm op v1 v2 ↪* v_x -> e ↪* v_x).
Proof.
  unfold refinement_open. simpl; intros. invclear H; mydestr.
  unfold termRraw.
  assert ([] ⊢t eval_op_under_bound_tm op v1 v2 ⋮t ret_ty_of_op op); auto.
  denotation_simp.
  apply H2; refinement_solver.
  unfold bstate_insert. dec_solver2.
Qed.

Lemma fst_ty_of_op_implies_nat:
  forall m bst st op n d ϕ (v: value),
    ({m;bst;st}⟦[v:fst_ty_of_op op|n|d|ϕ]⟧) v -> (exists (n: nat), v = n).
Proof.
  intros. invclear H; mydestr. simpl in H0. denotation_simp.
  destruct op; destruct x; simpl in H3; invclear H3; eauto.
Qed.

Lemma snd_ty_of_op_implies_nat:
  forall m bst st op n d ϕ (v: value),
    ({m;bst;st}⟦[v:snd_ty_of_op op|n|d|ϕ]⟧) v -> (exists (n: nat), v = n).
Proof.
  intros. invclear H; mydestr. simpl in H0. denotation_simp.
  destruct op; destruct x; simpl in H3; invclear H3; eauto.
Qed.

Lemma rR_basety_implies_nat:
  forall m bst st b n d ϕ (v: value),
    ({m;bst;st}⟦[v:b|n|d|ϕ]⟧) v -> (exists (c: constant), v = c).
Proof.
  intros. invclear H; mydestr. simpl in H0. denotation_simp.
  destruct x; simpl in H; invclear H; eauto.
Qed.

Lemma has_basety_implies_constant_or_var: forall Γ (b: base_ty) (v: value),
    Γ ⊢t v ⋮v b -> ((exists (n: constant), v = n) \/ (exists (y: atom), v = y)).
Proof.
  intros.
  destruct v.
  + left. eexists; eauto.
  + right. eexists; eauto.
  + invclear H.
  + invclear H.
  + invclear H.
Qed.

Lemma not_in_aset_implies_same_insert_refinement: forall (d: aset) (ϕ: refinement),
    not_fv_in_refinement d ϕ ->
    forall (x: atom), x ∉ d -> forall (m: state), forall bst v_x (v: constant), ϕ bst ({x  ↦ v_x} m) v <-> ϕ bst m v.
Proof.
  intros. apply H. intros.
  destruct v_x; simpl; auto; var_dec_solver2;
    assert (x <> x0) by fast_set_solver; my_simplify_map_eq3.
  destruct (m!!atom); my_simplify_map_eq3.
Qed.

Lemma refinement_shadow_update_st: forall bst v_x n ϕ (x: atom) d st (v: constant),
    x ∉ d -> wf_r n d ϕ -> ϕ bst ({ x ↦ v_x } st) v <-> ϕ bst st v.
Proof.
  intros.
  eapply not_in_aset_implies_same_insert_refinement; eauto. refinement_solver.
Qed.

Ltac rR_shadow_update_st_tac :=
  repeat match goal with
    | [H: valid_rty {v: _ |_ |?d|?ϕ} |- ?ϕ _ ({ _ ↦ _ } _) _ ] =>
        rewrite refinement_shadow_update_st with (d:=d); auto; refinement_solver
    | [H: valid_rty [v: _ |_ |?d|?ϕ] |- ?ϕ _ ({ _ ↦ _ } _) _ ] =>
        rewrite refinement_shadow_update_st with (d:=d); auto; refinement_solver
    | [H: valid_rty {v: _ |_ |?d|?ϕ}, H': ?ϕ _ ({ _ ↦ _ } _) _ |- ?ϕ _ _ _ ] =>
        rewrite refinement_shadow_update_st with (d:=d) in H'; auto; refinement_solver
    | [H: valid_rty [v: _ |_ |?d|?ϕ], H': ?ϕ _ ({ _ ↦ _ } _) _ |- ?ϕ _ _ _ ] =>
        rewrite refinement_shadow_update_st with (d:=d) in H'; auto; refinement_solver
    | [H: closed_rty _ _ ?τ, H': ?ϕ ?bst _ ?c_x |- ?ϕ ?bst _ ?c_x] =>
        match τ with
        | context [ϕ] => destruct H; mydestr
        end
    end.

Lemma rR_shadow_update_st: forall τ n st,
    closed_rty n (dom aset st) τ ->
    (forall bst (a: atom) (c: value) e, a ∉ (rty_fv τ) ->
                                   ({n; bst; { a ↦ c } st}⟦τ⟧) e <-> ({n; bst; st}⟦τ⟧) e
    ).
Proof.
  induction τ; split; simpl; intros; mydestr; subst;
    split; auto; split; try closed_rty_solver.
  - exists x. repeat split; auto. rR_shadow_update_st_tac.
  - exists x. repeat split; auto. rR_shadow_update_st_tac.
  - intros. apply H3; auto. rR_shadow_update_st_tac.
  - intros. apply H3; auto. rR_shadow_update_st_tac.
  - eexists; split; eauto.
    intros. refinement_simp1. apply H4 in H5. apply IHτ in H5; auto; refinement_solver7.
    rewrite refinement_shadow_update_st with (d:=d); auto; refinement_solver.
  - eexists; split; eauto.
    intros. refinement_simp1. apply H4 in H5. apply IHτ; auto; refinement_solver7.
    rewrite <- refinement_shadow_update_st with (d:=d); auto; refinement_solver.
  - eexists; split; eauto.
    intros. refinement_simp1.
    rewrite <- IHτ1 with (a:= a) (c:=c) in H5; auto; refinement_solver.
    apply H4 in H5. rewrite IHτ2 in H5; refinement_solver7.
  - eexists; split; eauto. intros. refinement_simp1.
    rewrite IHτ1 in H5 by refinement_solver.
    apply H4 in H5; rewrite IHτ2; auto; refinement_solver7.
Qed.

Lemma rR_shadow_update_st_c: forall τ n st,
    closed_rty n (dom aset st) τ ->
    (forall bst (a: atom) (c: constant) e, a ∉ (rty_fv τ) ->
                                      ({n; bst; <[a:=c]> st}⟦τ⟧) e <-> ({n; bst; st}⟦τ⟧) e
    ).
Proof.
  intros. eapply rR_shadow_update_st with (c:=c) in H; eauto.
Qed.

Lemma lc_rR_shadow_update_st: forall τ st (a: atom) c e,
    closed_rty 0 (dom aset st) τ -> a ∉ (rty_fv τ) ->
    ({ { a ↦ c } st}⟦τ⟧) e <-> ({st}⟦τ⟧) e.
Proof.
  split; intros.
  - rewrite rR_shadow_update_st in H1; eauto.
  - rewrite rR_shadow_update_st; eauto.
Qed.

Lemma lc_rR_shadow_update_st_c: forall τ st (a: atom) c e,
    closed_rty 0 (dom aset st) τ -> a ∉ (rty_fv τ) ->
    ({ <[a:=c]> st}⟦τ⟧) e <-> ({st}⟦τ⟧) e.
Proof.
  intros. eapply lc_rR_shadow_update_st with (c:=c) in H; eauto.
Qed.

Lemma subst_insert_lookup_neq_Some {A:Type}: forall (a b: atom) (c0 c1: A) (st: amap A),
    a <> b -> st !! a = Some c1 -> <[b:=c0]> st !! a = Some c1.
Proof.
  intros. setoid_rewrite lookup_insert_Some; auto.
Qed.

Lemma subst_insert_lookup_neq_None {A:Type}: forall (a b: atom) (c0: A) (st: amap A),
    a <> b -> st !! a = None -> <[b:=c0]> st !! a = None.
Proof.
  intros. setoid_rewrite lookup_insert_None; auto.
Qed.

Ltac amap_solver1 Hsta :=
  repeat match goal with
    | [|- <[?a:=_]> (<[?b:=_]> ?st) = <[?b:=_]> (<[?a:=_]> ?st)] =>
        setoid_rewrite (insert_commute st a b); auto; try fast_set_solver
    | [H: ?st !! ?a = None |- context [<[?b:=?c0]> ?st !! ?a ] ] =>
        setoid_rewrite (subst_insert_lookup_neq_None a b c0); auto; try fast_set_solver
    | [H: ?st !! ?a = Some ?c1 |- context [<[?b:=?c0]> ?st !! ?a ] ] =>
        setoid_rewrite (subst_insert_lookup_neq_Some a b c0 c1); auto; try fast_set_solver
    | [|- context [<[?b:=?c0]> ?st !! ?a ] ] =>
        destruct (st !! a) eqn: Hsta
    end.

Lemma subst_st_insert_commute:forall (v_x: value) (a b: atom) (c: constant) st,
    fv_value v_x ∩ {[a; b]} = ∅ ->
    a <> b -> ({a↦v_x}) (<[b:=c]> st) = (<[b:=c]>) ({a↦v_x} st).
Proof.
  destruct v_x; intros; simpl; auto.
  - amap_solver1 Hsta.
  - simpl. my_simplify_map_eq.
    amap_solver1 Hsta1. amap_solver1 Hsta2. set_solver. set_solver.
Qed.

Lemma insert_constant_in_st: forall (v_x: constant) (a: atom) (st: state),
    a ∉ (dom aset st) -> (dom aset (({a↦v_x}) st)) ≡ ({[a]} ∪ dom aset st).
Proof.
  intros; simpl; auto. my_simplify_map_eq2.
Qed.

Lemma insert_vfvar_in_st: forall (v_x: atom) (a: atom) (st: state),
    v_x ∈ dom aset st -> a ∉ (dom aset st) ->
    (dom aset (({a↦v_x}) st)) ≡ ({[a]} ∪ dom aset st).
Proof.
  intros; simpl; auto.
  - simpl in H. my_simplify_map_eq2.
Qed.

Ltac ok_dctx_solver_slow :=
  match goal with
  | [H1: ok_dctx ?d1 ?τ, H2: ok_dctx ?d2 ?τ |- ok_dctx ?d3 ?τ ] =>
      apply (ok_dctx_cap τ d1 d2 d3); auto; simpl; refinement_set_simp; set_solver
  | [H: ok_dctx ?d1 ?τ |- ok_dctx ?d2 ?τ ] =>
      apply (ok_dctx_trans τ d1 d2); simpl; auto; refinement_set_simp; set_solver
  end.

Ltac auto_ty_exfalso1 :=
  match goal with
  | [H: [] ⊢t (vfvar _) ⋮v _ |- _ ] => invclear H; listctx_set_simpl
  | [H: [] ⊢t (vbvar _) ⋮v _ |- _ ] => invclear H
  | [H: is_arr {v:_|_|_|_} |- _ ] => invclear H
  | [H: is_arr [v:_|_|_|_] |- _ ] => invclear H
  | [H: ¬ is_arr ?r, H': [] ⊢t vlam _ _ ⋮v ⌊?r⌋ |- _ ] => (destruct r; invclear H'; exfalso; auto)
  | [H: ¬ is_arr ?r, H': [] ⊢t vfix _ _ ⋮v ⌊?r⌋ |- _ ] => (destruct r; invclear H'; exfalso; auto)
  | [H: is_arr ?r, H': [] ⊢t (vconst _) ⋮v ⌊?r⌋ |- _ ] => (destruct r; invclear H'; invclear H)
  | [H: not_overbasety {v: _ |_|_|_} |- _ ] => invclear H
  end.

Ltac auto_ty_exfalso2 :=
  repeat (match goal with
          | [H: ¬ not_overbasety ?τ |- _ ] =>
              match τ with
              | {v:_|_|_|_} => clear H
              | [v:_|_|_|_] => exfalso; apply H; simpl; auto
              | (-:{v:_|_|_|_}⤑ _) => exfalso; apply H; simpl; auto
              | (_ ⤑ _) => exfalso; apply H; simpl; auto
              | _ => destruct τ
              end
          end || auto_ty_exfalso1).

Lemma auto_ty_base: forall τ_x,
    not_overbasety τ_x -> ¬ is_arr τ_x -> (exists b n d ϕ, τ_x = [v:b|n|d|ϕ]).
Proof.
  intros. destruct τ_x; invclear H.
  - eauto.
  - neg_apply H0; simpl; auto.
  - neg_apply H0; simpl; auto.
Qed.

Ltac auto_ty_exfalso3 :=
  match goal with
  | [H: not_overbasety ?τ_x, H': ¬ is_arr ?τ_x |- _ ] =>
      apply auto_ty_base in H; auto; mydestr; subst; try clear H'
  end || auto_ty_exfalso2.

Lemma is_arr_is_not_constant: forall r (x:constant), is_arr r -> ~ ([] ⊢t x ⋮v ⌊r⌋).
Proof.
  intros. destruct r; simpl; auto.
  - intro Hz. invclear Hz.
  - intro Hz. invclear Hz.
Qed.

Lemma rty_open_perserve_not_overbasety: forall τ k v, not_overbasety ({k ~r> v} τ) <-> not_overbasety τ.
Proof.
  induction τ; simpl; intros; auto.
Qed.

Lemma valid_rty_open: forall B n d ϕ (c: constant),
    valid_rty {v:B|S n|d|ϕ} -> valid_rty {v:B|n|d|refinement_open n c ϕ}.
Proof.
  intros. invclear H. invclear H1. constructor; auto. constructor; auto.
  - unfold not_fv_in_refinement in H. unfold not_fv_in_refinement. intros. apply H; auto.
  - unfold bound_in_refinement. unfold bound_in_refinement in H0.
    intros. unfold refinement_open. apply H0.
    unfold bst_eq. intros. unfold bstate_insert. dec_solver1. apply H1. lia.
Qed.

Lemma bst_eq_insert_S: forall m bst bst' c, bst_eq m bst bst' -> bst_eq (S m) (<b[m:=c]> bst) (<b[m:=c]> bst').
Proof.
  unfold bst_eq; intros.
  unfold bstate_insert. repeat var_dec_solver. apply H. lia.
Qed.

Lemma bst_eq_insert_same: forall m n bst bst' c, bst_eq m bst bst' -> bst_eq m (<b[n:=c]> bst) (<b[n:=c]> bst').
Proof.
  unfold bst_eq; intros.
  unfold bstate_insert. repeat var_dec_solver.
Qed.

Lemma bound_in_refinement_btrans: forall n m c ϕ,
    n ≤ S m ->
    bound_in_refinement n ϕ ->
    bound_in_refinement (n `min` m) (λ (bst : bstate) (st0 : state) (v : constant), ϕ (<b[m:=c]> bst) st0 v).
Proof.
  unfold bound_in_refinement; intros.
  destruct (decide (n = S m)); subst.
  - rewrite min_r in H1; try lia. apply H0. apply bst_eq_insert_S; auto.
  - rewrite min_l in H1; try lia. apply H0. apply bst_eq_insert_same; auto.
Qed.

Lemma wf_r_btrans: forall n m c d ϕ,
    n ≤ S m -> wf_r n d ϕ ->
    wf_r (n `min` m) d (λ (bst : bstate) (st0 : state) (v : constant), ϕ (<b[m:=c]> bst) st0 v).
Proof.
  intros. invclear H0. constructor; auto.
  - unfold not_fv_in_refinement. intros. apply H1; auto.
  - apply bound_in_refinement_btrans; auto.
Qed.

Global Hint Resolve wf_r_btrans: core.

Lemma not_overbasety_open_trans: forall τ m c,
    not_overbasety τ -> not_overbasety ({m ~r> c} τ).
Proof.
  induction τ; simpl; intros; auto.
Qed.

Global Hint Resolve not_overbasety_open_trans: core.

Lemma valid_rty_btrans: forall τ m (c: constant),
  lc_rty_idx (S m) τ -> valid_rty τ -> valid_rty ({m ~r> c} τ).
Proof.
  induction τ; simpl; unfold refinement_open; intros.
  - invclear H0; invclear H; constructor; eauto.
  - invclear H0; invclear H; constructor; eauto.
  - invclear H0; invclear H; constructor; eauto.
  - invclear H0; invclear H; constructor; auto; fold rty_open; eauto.
Qed.

Global Hint Resolve valid_rty_btrans: core.

Lemma lc_rty_idx_rty_btrans: forall τ m (c: constant),
  lc_rty_idx (S m) τ -> lc_rty_idx m ({m ~r> c} τ).
Proof.
  induction τ; simpl; intros; invclear H; constructor; auto; lia.
Qed.

Global Hint Resolve lc_rty_idx_rty_btrans: core.

Lemma rty_fv_open_c_eq: forall τ m (c: constant),
    rty_fv ({m ~r> c} τ) ≡ rty_fv τ.
Proof.
  induction τ; simpl; unfold refinement_set_open; intros; auto.
  - rewrite IHτ; auto.
  - rewrite IHτ1; auto. rewrite IHτ2; auto.
Qed.

Lemma closed_rty_open_trans: forall τ m d (c: constant),
    closed_rty (S m) d τ ->
    closed_rty m d ({m ~r> c} τ).
Proof.
  induction τ; intros; invclear H; constructor; auto.
  - rewrite rty_fv_open_c_eq; auto.
  - rewrite rty_fv_open_c_eq; auto.
Qed.

Global Hint Resolve closed_rty_open_trans: core.

Lemma is_arr_open_trans': forall τ_x k (v2: value),
  is_arr ({k ~r> v2} τ_x) -> is_arr τ_x.
Proof.
  intros. destruct τ_x; auto.
Qed.

Global Hint Resolve is_arr_open_trans': core.

Lemma is_arr_open_trans: forall τ_x k (v2: value),
  is_arr τ_x -> is_arr ({k ~r> v2} τ_x).
Proof.
  intros. destruct τ_x; auto.
Qed.

Global Hint Resolve is_arr_open_trans: core.

Lemma rty_open_perserve_erase: forall τ x k, ⌊{k ~r> x} τ ⌋ = ⌊τ⌋.
Proof.
  induction τ; simpl; intros; auto.
  - rewrite IHτ; auto.
  - rewrite IHτ1; auto. rewrite IHτ2; auto.
Qed.

Ltac auto_ty_exfalso4 :=
  match goal with
  | [H: ?P, H': ~ ?P |- _ ] => apply H' in H; invclear H
  | [H: is_arr [v:_|_|_|_] |- _ ] =>invclear H
  | [H: is_arr {v:_|_|_|_} |- _ ] =>invclear H
  | [H: {v:_|_|_|_} = [v:_|_|_|_] |- _] => invclear H
  | [H: [v:_|_|_|_] = {v:_|_|_|_} |- _] => invclear H
  | [H: {v:_|_|_|_} = {v:_|_|_|_} |- _] => invclear H
  | [H: [v:_|_|_|_] = [v:_|_|_|_] |- _] => invclear H
  | [H: is_arr ?r, H': [] ⊢t (vconst _) ⋮v ⌊ ?r ⌋ |- _ ] => eapply is_arr_is_not_constant in H; apply H in H'; invclear H'
  | [H: is_arr ?τ, H': ~ is_arr ({?k ~r> ?v} ?τ) |- _ ] =>
      assert (is_arr ({k ~r> v} τ)) by eauto; exfalso; auto
  | [H: ~ is_arr ?τ, H': is_arr ({?k ~r> ?v} ?τ) |- _ ] =>
      assert (is_arr τ) by eauto; exfalso; auto
  | [H: is_arr ?τ_x, H': {v:_|_|_|_} = {?k ~r> ?v2} ?τ_x |- _ ] =>
      assert (is_arr ({k ~r> v2} τ_x)) as Htmp by eauto;
      rewrite <- H' in Htmp; auto_ty_exfalso2
  | [H: is_arr ?τ_x, H': [v:_|_|_|_] = {?k ~r> ?v2} ?τ_x |- _ ] =>
      assert (is_arr ({k ~r> v2} τ_x)) as Htmp by eauto;
      rewrite <- H' in Htmp; auto_ty_exfalso2
  end || auto_ty_exfalso3.

Ltac auto_ty_exfalso := auto_ty_exfalso4.

Lemma over_inhabitant_only_constant: forall (u: value) st b n d ϕ,
    ({0;b∅;st}⟦{v:b|n|d|ϕ}⟧) u -> (exists (c: constant), u = c).
Proof.
  intros. invclear H; mydestr. exists x. invclear H3. auto.
Qed.

Lemma state_subst_implies_rty_subst_eq2_forward_ok_dctx
    : ∀ (a v : atom) (Γ : list (atom * rty)) (L : aset) (c_x : constant) (x : atom)
      (k : nat) (b : base_ty) (n : nat) (d : aset) (ϕ : refinement),
  not_fv_in_refinement d ϕ -> a ∈ L ->
  bound_in_refinement (n `min` k) (refinement_open k c_x ϕ) ->
  ok_dctx L (Γ ++ [(x, {k ~r> v} [v:b|n|d|ϕ])]) ->
  ok_dctx L (Γ ++ [(x, {k ~r> {a := c_x }v v} [v:b|n|d|ϕ])]).
Proof.
  intros a v. induction Γ; intros.
  - denotation_simp. destruct (decide (a = v)); subst; auto.
    invclear H2; auto_ty_exfalso. constructor; auto.
    invclear H7. constructor; auto.
    + invclear H2. constructor; auto. invclear H7. constructor; auto.
      unfold not_fv_in_refinement. intros. apply H. intros. apply H7; auto.
    + invclear H3. constructor; auto.
    + simpl in H4. simpl. set_solver.
  - mydestr. invclear H2; auto_ty_exfalso.
    + constructor; auto; fold (@app (atom * rty)). listctx_set_simpl.
      eapply IHΓ; eauto. set_solver.
    + apply ok_dctx_cons_arr; auto; fold (@app (atom * rty)). listctx_set_simpl.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma bstate_insert_commute: forall n1 n2 c0 c x,
    n1 <> n2 ->
    (<b[n2:=c0]> (<b[n1:=c]> x)) = (<b[n1:=c]> (<b[n2:=c0]> x)).
Proof.
  unfold bstate_insert. intros.
  apply functional_extensionality; intros.
  dec_solver2.
Qed.

Lemma rty_open_commute: forall n1 n2 (v1 v2: value) b d n ϕ,
    lc v1 -> lc v2 -> n1 <> n2 ->
    {n1 ~r> v1} ({n2 ~r> v2} [v:b|d|n|ϕ]) = {n2 ~r> v2} ({n1 ~r> v1} [v:b|d|n|ϕ]).
Proof.
  intros. simpl. assert ((d `min` n2) `min` n1 = (d `min` n1) `min` n2). lia. rewrite H2. clear H2.
  assert (refinement_set_open n1 v1 (refinement_set_open n2 v2 n) = refinement_set_open n2 v2 (refinement_set_open n1 v1 n)).
  unfold refinement_set_open.
  destruct v1; destruct v2; auto. set_solver.
  rewrite H2. clear H2.
  assert (refinement_open n1 v1 (refinement_open n2 v2 ϕ) = refinement_open n2 v2 (refinement_open n1 v1 ϕ)).
  unfold refinement_open.
  do 3 (apply functional_extensionality; intros).
  destruct v1; destruct v2; try destruct (x0 !! atom); try destruct (x0 !! atom0); auto;
  try (rewrite bstate_insert_commute; auto).
  rewrite H2; auto.
Qed.

Lemma rty_open_commute_op: forall n1 n2 (v1 v2: value) op,
    lc v1 -> lc v2 -> n1 <> n2 ->
    {n1 ~r> v1} ({n2 ~r> v2} (mk_op_ret op)) = {n2 ~r> v2} ({n1 ~r> v1} (mk_op_ret op)).
Proof.
  intros. unfold mk_op_ret. rewrite rty_open_commute; auto.
Qed.

Lemma tletbiop_aux1: forall op (x1:atom),
    not_fv_in_refinement ({[x1]} ∪ ∅)
    (refinement_open 0 x1 (λ (bst : bstate) (_ : state) (v : constant), eval_op op (bst 0) (bst 1) v)).
Proof.
  intros. unfold not_fv_in_refinement. intros. unfold refinement_open.
  assert (m !! x1 = m' !! x1). apply H. set_solver.
  rewrite H0.
  destruct (m' !! x1); auto.
Qed.

Lemma tletbiop_aux2: forall op (x1:atom) (c_x:constant),
  bound_in_refinement 0
    (refinement_open 1 c_x
       (refinement_open 0 x1
          (λ (bst : bstate) (_ : state) (v : constant), eval_op op (bst 0) (bst 1) v))).
Proof.
  intros. unfold bound_in_refinement. intros. unfold refinement_open.
  destruct (st !! x1); auto.
Qed.

Lemma subst_var_same_value: forall (x: atom) (v: value), {x := v }v x = v.
Proof. intros. simpl. dec_solver2. Qed.
Lemma subst_var_same_tm: forall (x: atom) (v: value), {x := v }t x = v.
Proof. intros. simpl. dec_solver2. Qed.
Lemma subst_var_diff_value: forall (x y: atom) (v: value), x <> y -> {x := v }v y = y.
Proof. intros. simpl. dec_solver2. Qed.
Lemma subst_var_diff_tm: forall (x y: atom) (v: value), x <> y -> {x := v }t y = y.
Proof. intros. simpl. dec_solver2. Qed.
Lemma tletbiop_aux3: forall (x1 x0: atom) (c_x: value),
    lc c_x -> lc ({x1 := c_x }v x0).
Proof. intros. simpl. dec_solver2. Qed.
Lemma tletbiop_aux4: forall (x1 x0: atom) (c_x: constant),
    lc ({x1 := c_x }v x0).
Proof. intros. apply tletbiop_aux3. auto. Qed.
Global Hint Resolve tletbiop_aux4: core.
Lemma tletbiop_aux5: forall (x1: atom) (x0 c_x: constant),
    lc ({x1 := c_x }v x0).
Proof. intros. simpl. auto. Qed.
Global Hint Resolve tletbiop_aux5: core.

Lemma subst_over_constant: forall (x: atom) (v: value) (c_x:constant), ({x := v }v c_x) = c_x.
Proof. intros. auto. Qed.

Ltac biop_simpl:=
  repeat
    match goal with
    | [H: context [{?x := ?v }v (vfvar ?x)] |- _ ] => rewrite (subst_var_same_value x v) in H
    | [H: context [{?x := ?v }t (tvalue (vfvar ?x))] |- _ ] => rewrite (subst_var_same_tm x v) in H
    | [|- context [{?x := ?v }v (vfvar ?x)] ] => rewrite (subst_var_same_value x v)
    | [|- context [{?x := ?v }t (tvalue (vfvar ?x))] ] => rewrite (subst_var_same_tm x v)
    | [H: context [{?x := ?v }v (vfvar ?y)] |- _ ] =>
        assert (x <> y) as Htmp by auto;
        rewrite (subst_var_diff_value x y v Htmp) in H;
        try clear Htmp
    | [H: context [{?x := ?v }t (tvalue (vfvar ?y))] |- _ ] =>
        assert (x <> y) as Htmp by auto;
        rewrite (subst_var_diff_tm x y v Htmp) in H;
        try clear Htmp
    | [|- context [{?x := ?v }v (vfvar ?y)] ] =>
        assert (x <> y) as Htmp by auto;
        rewrite (subst_var_diff_value x y v Htmp);
        try clear Htmp
    | [|- context [{?x := ?v }t (tvalue (vfvar ?y))] ] =>
        assert (x <> y) as Htmp by auto;
        rewrite (subst_var_diff_tm x y v Htmp);
        try clear Htmp
    | [H: context [{?x := ?v }v (vconst ?c_x) ] |- _ ] =>
        rewrite (subst_over_constant x v c_x) in H
    | [|- context [{?x := ?v }v (vconst ?c_x) ] ] =>
        rewrite (subst_over_constant x v c_x)
    end.

Lemma bstate_insert_insert:
  ∀ (n1 : nat) (c0 c : constant) (x : bstate), <b[n1:=c0]> (<b[n1:=c]> x) = <b[n1:=c0]> x.
Proof.
  intros. unfold bstate_insert. apply functional_extensionality; intros.
  dec_solver2.
Qed.

Lemma denotation_st_update_iff_subst:
  forall τ (z: atom) (c: constant) n bst (st: state) e,
    z ∉ (dom aset st) ->
    ({n;bst;<[z:=c]> st}⟦τ⟧ e) <-> (closed_rty n ({[z]} ∪ dom aset st) τ /\ {n;bst;st}⟦({z:=c}r) τ⟧ e).
Proof.
  induction τ; split; simpl; intros; mydestr; subst.
  - do 2 (split; denotation_simp; auto). split; auto.
    + eapply closed_rty_subst_excluded_forward in H1; eauto.
    + unfold refinement_subst. unfold state_subst. dec_solver3.
      repeat eexists; eauto. rewrite closed_rty_over_implies_state_dummy_insert in H3; eauto.
  - split; auto. split; auto.
    + denotation_simp.
    + repeat eexists; eauto.
      unfold refinement_subst in H4. unfold refinement_subst in H2.
      unfold refinement_set_subst in H2.
      unfold state_subst in H2. unfold state_subst in H4.
      dec_solver3.
      rewrite closed_rty_over_implies_state_dummy_insert; eauto.
  - split; auto; denotation_simp. split; auto. split; auto.
    + eapply closed_rty_subst_excluded_forward in H1; eauto.
    + unfold refinement_subst. unfold state_subst. dec_solver3.
      intros. apply H2; auto. rewrite closed_rty_under_implies_state_dummy_insert; eauto.
  - split; auto. split; auto.
    + denotation_simp.
    + repeat eexists; eauto. intros. apply H3; auto.
      unfold refinement_subst. unfold refinement_subst in H2. unfold refinement_set_subst in H2. unfold state_subst. unfold state_subst in H2.
      dec_solver3.
      rewrite closed_rty_under_implies_state_dummy_insert in H5; eauto.
  - split; auto; denotation_simp. split; auto; ctx_erase_simp4. split; auto.
    + eapply closed_rty_subst_excluded_forward in H1; eauto.
    + eexists; split; eauto. intros. unfold refinement_subst in H5.
      assert (ϕ bst (<[z:=c]> st) c_x).
      { unfold state_subst in H5.
        unfold state_subst in H3.
        dec_solver3; auto. rewrite wf_r_implies_state_dummy_insert; eauto. refinement_solver7. }
      apply H3 in H6; auto. rewrite IHτ in H6; mydestr; auto.
  - split; auto; ctx_erase_simp4. split; auto.
    + denotation_simp.
    + eexists; split; eauto. intros. rewrite IHτ; auto. split; refinement_solver.
      apply H4; auto.
      unfold refinement_subst. unfold state_subst. unfold state_subst in H4. dec_solver3.
      invclear H2. invclear H5.
      rewrite wf_r_implies_state_dummy_insert in H6; eauto. refinement_solver7.
  - split; auto; denotation_simp. split; auto; ctx_erase_simp4. split; auto.
    + eapply closed_rty_subst_excluded_forward in H1; eauto.
    + eexists; split; eauto. intros.
      assert (({n;bst;<[z:=c]> st}⟦τ1⟧) v_x) as HH. rewrite IHτ1; auto. split; refinement_solver7.
      apply H3 in HH. rewrite IHτ2 in HH; auto. mydestr; auto.
  - split; auto; ctx_erase_simp4. split; auto; denotation_simp.
    + eexists; split; eauto. intros. rewrite IHτ2; auto. split; refinement_solver. apply H4. rewrite IHτ1 in H5; auto. mydestr; auto.
Qed.

Lemma state_insert_insert_neq: forall (a b: atom) (c_a: constant) (v_b: value) (st: state),
    a <> b -> a ∉ fv_value v_b ->
    {a ↦ c_a} ({b ↦ v_b} st) = {b ↦ v_b} ({a ↦ c_a} st).
Proof.
  intros. destruct v_b; simpl; auto.
  - setoid_rewrite insert_commute at 1; auto.
  - assert (a <> atom) by fast_set_solver. my_simplify_map_eq3.
    destruct (st !! atom) eqn:Hst; my_simplify_map_eq3.
    setoid_rewrite insert_commute at 1; auto.
Qed.

Lemma state_insert_insert_neq_better: forall (a b: atom) (c_a: constant) (v_b: value) (st: state),
    a <> b -> v_b <> a ->
    {a ↦ c_a} ({b ↦ v_b} st) = {b ↦ v_b} ({a ↦ c_a} st).
Proof.
  intros. destruct v_b; auto.
  - apply state_insert_insert_neq; auto. set_solver.
  - apply state_insert_insert_neq; auto. set_solver.
Qed.

Lemma termR_implies_reduction_trans: forall T e e' (v: value),
  e <-<{ []; T} e' -> e ↪* v -> e' ↪* v.
Proof.
  intros. invclear H.
  assert (instantiation [] []); auto.
  eapply (H3 _ v) in H; auto.
Qed.

Global Hint Resolve termR_implies_reduction_trans: core.

Lemma termR_perserve_rR: forall τ (e e': tm),
    not_overbasety τ ->
    valid_rty τ ->
    e <-<{[]; ⌊ τ ⌋ } e' -> (forall n bst st, {n;bst;st}⟦τ⟧ e -> {n;bst;st}⟦τ⟧ e').
Proof.
  induction τ; simpl; intros; invclear H0; mydestr; subst.
  - invclear H.
  - repeat (split; try termR_solver).
  - repeat (split; try termR_solver).
    eexists; split; eauto.
  - repeat (split; try termR_solver).
    eexists; split; eauto.
  - repeat (split; try termR_solver).
    eexists; split; eauto.
Qed.

Lemma termR_perserve_rR_over: forall b n1 d ϕ (e e': value),
    valid_rty {v:b|n1|d|ϕ} ->
    e' <-<{[]; b } e ->
    (forall n bst st, {n;bst;st}⟦{v:b|n1|d|ϕ}⟧ e -> {n;bst;st}⟦{v:b|n1|d|ϕ}⟧ e').
Proof.
  intros. inversion H1; mydestr; subst.
  repeat (split; try termR_solver). denotation_simp3; subst.
  exists x. do 2 (split; auto). rewrite termR_value_iff_same in H0; mydestr; denotation_simp3.
Qed.

(* terr *)

Lemma terr_is_not_inhabitant_of_overbase: forall τ n bst st,
    {n; bst; st}⟦τ⟧ terr -> not_overbasety τ.
Proof.
  destruct τ; intros; invclear H; mydestr; simpl; auto.
  invclear H3.
Qed.

Lemma rR_inhabitant_err_or_halt: forall τ,
    valid_rty τ ->
    (forall n bst st, (∀ e, ({n;bst;st}⟦τ⟧) e -> (exists (v: value), e ↪* v)) \/ (({n;bst;st}⟦τ⟧) terr)).
Proof.
  intros τ Hv. induction Hv; intros.
  - left. intros. invclear H0; mydestr; subst. eexists; eauto.
  - destruct (classic (({n0;bst;st}⟦[v:B|n|d|ϕ]⟧) terr)); auto. left; intros.
    neg_apply H0. invclear H1; mydestr. do 2 (split; auto). intros.
    apply H3 in H5; auto. exfalso_apply H2.
  - left. intros. simpl in H1; mydestr. eexists; eauto.
  - left. intros. simpl in H0; mydestr. eexists; eauto.
  - left. intros. simpl in H0; mydestr. eexists; eauto.
Qed.

Lemma not_rR_inhabitant_err_implies_halt: forall τ n bst st,
    valid_rty τ -> ~ ({n;bst;st}⟦τ⟧) terr -> ∀ e, ({n;bst;st}⟦τ⟧) e -> (exists (v: value), e ↪* v).
Proof.
  intros.
  eapply rR_inhabitant_err_or_halt in H. destruct H; eauto.
  exfalso_apply H.
Qed.

Global Hint Constructors multistep: core.

Lemma is_arr_implies_random_inhabitant_is_value: forall τ_x, is_arr τ_x -> (exists (v: value), random_inhabitant τ_x = v).
Proof.
  induction τ_x; simpl; intro; invclear H; eauto.
Qed.

Lemma mk_eq_constant_is_not_overbasety: forall c, not_overbasety (mk_eq_constant c).
Proof.
  intros. destruct c; simpl; auto.
Qed.

Global Hint Resolve mk_eq_constant_is_not_overbasety: core.

Lemma mk_eq_var_is_not_overbasety: forall b x, not_overbasety (mk_eq_var b x).
Proof.
  intros. destruct b; simpl; auto.
Qed.

Global Hint Resolve mk_eq_var_is_not_overbasety: core.

Lemma is_arr_implies_not_overbasety: forall τ, is_arr τ -> not_overbasety τ.
Proof.
  intros. destruct τ; simpl; auto; invclear H; auto.
Qed.

Global Hint Resolve is_arr_implies_not_overbasety: core.

Lemma random_inhabitant_in_any_under: ∀ (τ: rty) (bst : bstate) n st,
    not_overbasety τ ->
    closed_rty n (dom _ st) τ ->
    ({n;bst;st}⟦τ⟧) (random_inhabitant τ).
Proof.
  induction τ; intros; invclear H; mydestr.
  - destruct B.
    + do 2 (split; simpl; auto).
      intros. destruct c; invclear H.
      apply mk_nat_gen_reduce_to_all_nat.
    + do 2 (split; simpl; auto).
      intros. destruct c; invclear H.
      apply mk_bool_gen_reduce_to_all_bool.
  - denotation_simp. split. basic_typing_solver6. split; refinement_solver7.
    + eexists; split; eauto. apply multistep_refl.
      assert (lc (random_inhabitant (-:{v: B | n | d | ϕ}⤑ τ))); auto.
      intros.
      apply termR_perserve_rR with (e:= (random_inhabitant τ)); refinement_solver7.
      assert
        ((random_inhabitant τ ^t^ c_x) <-<{ []; ⌊τ⌋} (mk_app (vlam B (random_inhabitant τ)) c_x)). apply mk_app_reduce_to_open'; auto; basic_typing_solver6.
      reduction_simpl1.
  - denotation_simp. split. basic_typing_solver6. split; refinement_solver7.
    + eexists; split; eauto. apply multistep_refl.
      assert (lc (random_inhabitant (τ1 ⤑ τ2))); auto.
      intros.
      apply IHτ1 with (bst:=bst) in H; auto.
      apply IHτ2 with (bst:=bst) in H0; auto.
      apply termR_perserve_rR with (e:= tlete v_x (random_inhabitant τ2)); refinement_solver7.
      apply mk_app_reduce_to_let'; auto; refinement_solver7; basic_typing_solver7.
      apply termR_perserve_rR with (e:= random_inhabitant τ2); refinement_solver7.
      eapply let_value_in_lc_termR_drop; eauto. refinement_solver.
Qed.

Global Hint Resolve terr_is_not_inhabitant_of_overbase: core.

(** term meet *)
Lemma rR_tmeet_when_both: forall n bst st b n1 d ϕ e1 e2,
    ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e1 -> ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e2 ->
    ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) (e1 ⊗{ b } e2).
Proof.
  intros. invclear H; mydestr. constructor; auto. apply tmeet_typable; refinement_solver.
  constructor; auto.
  intros. rewrite reduction_tmeet_iff_both; refinement_solver.
Qed.

Lemma rR_tmeet3_when_all: forall n bst st b n1 d ϕ e1 e2 e3,
    ({n;bst;st}⟦ [v:b|n1|d|ϕ]  ⟧) e1 -> ({n;bst;st}⟦ [v:b|n1|d|ϕ]  ⟧) e2 -> ({n;bst;st}⟦ [v:b|n1|d|ϕ]  ⟧) e3 ->
    ({n;bst;st}⟦ [v:b|n1|d|ϕ]  ⟧) ((e1 ⊗{ b } e2) ⊗{ b } e3).
Proof.
  intros. apply rR_tmeet_when_both; auto. apply rR_tmeet_when_both; auto.
Qed.

Lemma rR_tmeet4_when_all: forall n bst st b n1 d ϕ e1 e2 e3 e4,
    ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e1 ->
    ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e2 -> ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e3 -> ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e4 ->
    ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) (((e1 ⊗{ b } e2) ⊗{ b } e3) ⊗{ b } e4).
Proof.
  intros. apply rR_tmeet_when_both; auto. apply rR_tmeet3_when_all; auto.
Qed.

Lemma rR_tmeet5_when_all: forall n bst st b n1 d ϕ e1 e2 e3 e4 e5,
    ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e1 -> ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e2 ->
    ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e3 -> ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e4 ->
    ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) e5 ->
    ({n;bst;st}⟦ [v:b|n1|d|ϕ] ⟧) ((((e1 ⊗{ b } e2) ⊗{ b } e3) ⊗{ b } e4) ⊗{ b } e5).
Proof.
  intros. apply rR_tmeet_when_both; auto. apply rR_tmeet4_when_all; auto.
Qed.

Lemma reduction_tmeet3_iff_all: forall (T: base_ty) e1 e2 e3,
    [] ⊢t e1 ⋮t T -> [] ⊢t e2 ⋮t T -> [] ⊢t e3 ⋮t T ->
    (forall (v: value), ((e1 ⊗{ T } e2) ⊗{ T } e3) ↪* v <-> e1 ↪* v /\ e2 ↪* v /\ e3 ↪* v).
Proof.
  intros. rewrite reduction_tmeet_iff_both; refinement_solver.
  rewrite reduction_tmeet_iff_both; refinement_solver.
  apply tmeet_typable; refinement_solver.
Qed.

Lemma reduction_tmeet4_iff_all: forall (T: base_ty) e1 e2 e3 e4,
    [] ⊢t e1 ⋮t T -> [] ⊢t e2 ⋮t T -> [] ⊢t e3 ⋮t T -> [] ⊢t e4 ⋮t T ->
    (forall (v: value),
        (((e1 ⊗{ T } e2) ⊗{ T } e3) ⊗{ T } e4) ↪* v <-> e1 ↪* v /\ e2 ↪* v /\ e3 ↪* v /\ e4 ↪* v).
Proof.
  intros. rewrite reduction_tmeet_iff_both; refinement_solver.
  rewrite reduction_tmeet3_iff_all; refinement_solver.
  apply tmeet_typable; refinement_solver.
  apply tmeet_typable; refinement_solver.
Qed.

Lemma reduction_tmeet5_iff_all: forall (T: base_ty) e1 e2 e3 e4 e5,
    [] ⊢t e1 ⋮t T -> [] ⊢t e2 ⋮t T -> [] ⊢t e3 ⋮t T -> [] ⊢t e4 ⋮t T -> [] ⊢t e5 ⋮t T ->
    (forall (v: value),
        ((((e1 ⊗{ T } e2) ⊗{ T } e3) ⊗{ T } e4) ⊗{ T } e5) ↪* v <->
          e1 ↪* v /\ e2 ↪* v /\ e3 ↪* v /\ e4 ↪* v /\ e5 ↪* v).
Proof.
  intros. rewrite reduction_tmeet_iff_both; refinement_solver.
  rewrite reduction_tmeet4_iff_all; refinement_solver.
  apply tmeet_typable; refinement_solver.
  apply tmeet_typable; refinement_solver.
  apply tmeet_typable; refinement_solver.
Qed.

Ltac auto_meet_exists HE :=
  match goal with
     | [H1: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x1,
           H2: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x2,
             H3: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x3,
               H4: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x4,
                 H5: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x5
        |- ∃ e, {0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧ e /\ _ ] =>
         exists ((((x1 ⊗{ b } x2) ⊗{ b } x3) ⊗{ b } x4) ⊗{ b } x5)
         ; assert ( {0;b∅;st}⟦[v:b|n|d|ϕ]⟧ ((((x1 ⊗{ b } x2) ⊗{ b } x3) ⊗{ b } x4) ⊗{ b } x5))
           as HE by (eapply rR_tmeet5_when_all; auto); split; auto; intros
  | [H1: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x1,
        H2: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x2,
          H3: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x3,
            H4: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x4 |- ∃ e, {0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧ e /\ _ ] =>
      exists (((x1 ⊗{ b } x2) ⊗{ b } x3) ⊗{ b } x4) ;
      assert ( {0;b∅;st}⟦[v:b|n|d|ϕ]⟧ (((x1 ⊗{ b } x2) ⊗{ b } x3) ⊗{ b } x4)) as HE by (eapply rR_tmeet4_when_all; auto); split; auto; intros
  | [H1: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x1,
        H2: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x2,
          H3: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x3 |- ∃ e, {0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧ e /\ _ ] =>
      exists ((x1 ⊗{ b } x2) ⊗{ b } x3) ; assert ( {0;b∅;st}⟦[v:b|n|d|ϕ]⟧ ((x1 ⊗{ b } x2) ⊗{ b } x3)) as HE by (eapply rR_tmeet3_when_all; auto); split; auto; intros
  | [H1: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x1,
        H2: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x2 |- ∃ e, {0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧ e /\ _ ] =>
      exists (x1 ⊗{ b } x2); assert ( {0;b∅;st}⟦[v:b|n|d|ϕ]⟧ (x1 ⊗{ b } x2)) as HE by (eapply rR_tmeet_when_both; eauto); split; auto; intros
  | [H1: ({0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧) ?x1 |- ∃ e, {0;b∅;?st}⟦[v:?b|?n|?d|?ϕ]⟧ e /\ _ ] =>
      exists x1; split; eauto; intros
  | [|- ∃ e, {0;b∅;?st}⟦?r⟧ e /\ _ ] =>
      assert ({0;b∅;st}⟦r⟧ (random_inhabitant r)) by (apply random_inhabitant_in_any_under; refinement_solver7);
      eexists; split; eauto; intros
  end.

Ltac auto_meet_reduce :=
  match goal with
  | [H: ((((?x1 ⊗{ ?b } ?x2) ⊗{ ?b } ?x3) ⊗{ ?b } ?x4) ⊗{ ?b } ?x5) ↪* ?v |- _ ] =>
      rewrite reduction_tmeet5_iff_all in H; refinement_solver7; mydestr; eauto
  | [H: (((?x1 ⊗{ ?b } ?x2) ⊗{ ?b } ?x3) ⊗{ ?b } ?x4)↪* ?v |- _ ] =>
      rewrite reduction_tmeet4_iff_all in H; refinement_solver7; mydestr; eauto
  | [H: ((?x1 ⊗{ ?b } ?x2) ⊗{ ?b } ?x3) ↪* ?v |- _ ] =>
      rewrite reduction_tmeet3_iff_all in H; refinement_solver7; mydestr; eauto
  | [H: (?x1 ⊗{ ?b} ?x2) ↪* ?v |- _ ] =>
      rewrite reduction_tmeet_iff_both in H; refinement_solver7; mydestr; eauto
  end.

Ltac auto_under_specialize e :=
  repeat (match goal with
          | [He: ?P (tvalue e), H: forall e_x, ?P e_x -> _ |- _ ] => specialize (H _ He)
          | [He: ?P e, H: forall e_x, ?P e_x -> _ |- _ ] => specialize (H _ He)
          | [He: ?P (tvalue e), H: forall e_x, _ (tvalue e_x) -> _ |- _ ] => specialize (H _ He)
          | [He: ?P (tvalue (vconst e)), H: forall c_x, _ (tvalue (vconst c_x)) -> _ |- _ ] => specialize (H _ He)
          end; mydestr).

Ltac auto_under_reduction_specialize :=
  repeat match goal with
    | [H: forall v, ?e ↪* (tvalue _) → _, H': ?e ↪* (tvalue _) |- _ ] => specialize (H  _ H')
    end.

Ltac auto_under e :=
  auto_under_specialize e; auto_under_reduction_specialize.
