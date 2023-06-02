From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemanticsProp.
From CT Require Import BasicTypingProp.
From CT Require Import SyntaxSugar.
From CT Require Import RefinementType.
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

Lemma dom_insert_simp: forall (a: atom) (c_x: constant) (st: state),
    (dom aset (<[a:=c_x]> st)) = {[a]} ∪ dom aset st.
Proof.
  intros. my_set_solver.
Qed.

Ltac my_simplify_map_eq1 :=
  repeat (
      match goal with
      | [|- Some ?x = Some ?y] => assert (x = y); auto
      | [|- (?a = ?b) <-> (?a = ?c)] => assert (b = c) as Htmp; try rewrite Htmp; auto
      | [|- (?a = ?b) = (?a = ?c)] => assert (b = c) as Htmp; try rewrite Htmp; auto
      | [|- <[_:=_]> ?m !! ?x = ?m !! ?x] => setoid_rewrite lookup_insert_ne; simplify_map_eq; auto
      | [|- <[_:=_]> ?m !! ?x = Some _ ] => setoid_rewrite lookup_insert_ne; simplify_map_eq; auto
      | [|- Some _ = <[_:=_]> ?m !! ?x ] => setoid_rewrite lookup_insert_ne; simplify_map_eq; auto
      | [H: <[_:=_]> ?m !! ?x = Some _ |- ?m !! ?x = Some _] => setoid_rewrite lookup_insert_ne in H; auto; fast_set_solver
      | [H: Some _ = <[_:=_]> ?m !! ?x |- Some _ = ?m !! ?x ] => setoid_rewrite lookup_insert_ne in H; auto; fast_set_solver
      | [H: context [ dom aset (<[?a:=?c_x]> ?st) ] |- _ ] =>
          setoid_rewrite (dom_insert_simp a c_x st) in H
      | [ |- context [ dom aset (<[?a:=?c_x]> ?st) ]] =>
          setoid_rewrite (dom_insert_simp a c_x st)
      end || (simplify_map_eq; fast_set_solver)).

Ltac my_simplify_map_eq2 :=
  repeat (match goal with
          | [|- context [ <[?a:=_]> (<[?a:=_]> ?st) ]] =>
              setoid_rewrite insert_insert
          | [H: context [ <[?a:=_]> (<[?a:=_]> ?st) ] |- _ ] =>
              setoid_rewrite insert_insert in H
          | [|- context [<[?b:=?c0]> ?st !! ?b ] ] => setoid_rewrite lookup_insert
          | [H: context [<[?b:=?c0]> ?st !! ?b ] |- _ ] => setoid_rewrite lookup_insert in H
          | [H: ?st !! ?x = Some _ |- context [?st !! ?x]] => setoid_rewrite H
          | [H: ?x ∈ dom _ ?st |- context [?st !! ?x]] =>
              assert (exists c, st !! x = Some c) as Htmp by
                (destruct (st !! x) eqn: HH; eauto;
                 setoid_rewrite <- not_elem_of_dom in HH; set_solver); mydestr
          | [H': ?a ∉ dom _ ?st |- context [?st !! ?a]] =>
              assert (st !! a = None) as Htmp by (apply not_elem_of_dom; fast_set_solver);
              rewrite Htmp; try clear Htmp
          | [H': ?a ∉ dom _ ?st, H: context [?st !! ?a] |- _ ] =>
              assert (st !! a = None) as Htmp by (apply not_elem_of_dom; fast_set_solver);
              rewrite Htmp in H; try clear Htmp
          end || my_simplify_map_eq1).

Ltac my_simplify_map_eq3 :=
  repeat (match goal with
          | [H: ?x <> ?z |- context [<[?z:=_]> _ !! ?x ] ] =>
              setoid_rewrite lookup_insert_ne; eauto; try fast_set_solver
          | [H: ?z <> ?x |- context [<[?z:=_]> _ !! ?x ] ] =>
              setoid_rewrite lookup_insert_ne; eauto; try fast_set_solver
          | [H: ?x <> ?z, H': context [<[?z:=_]> _ !! ?x] |- _ ] =>
              setoid_rewrite lookup_insert_ne in H; eauto; try fast_set_solver
          | [H: ?z <> ?x, H': context [<[?z:=_]> _ !! ?x] |- _ ] =>
              setoid_rewrite lookup_insert_ne in H; eauto; try fast_set_solver
          | [H: ?x <> ?z |- context [(delete ?z _) !! ?x ] ] =>
              setoid_rewrite lookup_delete_ne; eauto; try fast_set_solver
          | [H: ?z <> ?x |- context [(delete ?z _) !! ?x ] ] =>
              setoid_rewrite lookup_delete_ne; eauto; try fast_set_solver
          | [H: ?x <> ?z, H': context [(delete ?z _) !! ?x] |- _ ] =>
              setoid_rewrite lookup_delete_ne in H; eauto; try fast_set_solver
          | [H: ?z <> ?x, H': context [(delete ?z _) !! ?x] |- _ ] =>
              setoid_rewrite lookup_delete_ne in H; eauto; try fast_set_solver
          | [H: context [(delete ?z _) !! ?z] |- _ ] =>
              setoid_rewrite lookup_delete in H; eauto; try fast_set_solver
          | [|- context [(delete ?z _) !! ?z] ] =>
              setoid_rewrite lookup_delete; eauto; try fast_set_solver
          end || my_simplify_map_eq2).

Ltac my_simplify_map_eq := my_simplify_map_eq3.

Lemma closed_rty_trans: forall n d1 d2 τ, d1 ⊆ d2 -> closed_rty n d1 τ -> closed_rty n d2 τ.
Proof.
  intros. invclear H0. constructor; auto. fast_set_solver.
Qed.

Lemma lc_rty_idx_under_0_is_0: forall b n d ϕ, lc_rty_idx 0 [v:b|n|d|ϕ] -> n = 0.
Proof.
  intros. invclear H. lia.
Qed.

Lemma lc_rty_idx_over_0_is_0: forall b n d ϕ, lc_rty_idx 0 {v:b|n|d|ϕ} -> n = 0.
Proof.
  intros. invclear H. lia.
Qed.

Lemma inv_neg_not_overbasety: forall r, ¬ not_overbasety r -> (exists b n d ϕ, r = {v:b|n|d|ϕ}).
Proof.
  intros. neg_apply H. destruct r; simpl; auto.
  eapply H0; eauto.
Qed.

Ltac refinement_simp1 :=
  listctx_set_simpl;
  repeat match goal with
    | [H: context [ rty_fv (-:{v: _ | _ | _ | _}⤑ _) ] |- _ ] => simpl in H
    | [H: context [ rty_fv (_ ⤑ _) ] |- _ ] => simpl in H
    | [H: ¬ not_overbasety _ |- _] => apply inv_neg_not_overbasety in H; mydestr; subst
    | [H: context [ dom aset ∅ ] |- _ ] =>
        assert (dom aset (∅: state) = ∅) as Htmp by my_simplify_map_eq;
        setoid_rewrite Htmp in H; try clear Htmp
    | [H: lc_rty_idx 0 [v:_|?n|_|_] |- _ ] =>
        match n with
        | 0 => fail 1
        | _ =>  assert (n = 0) by (apply lc_rty_idx_under_0_is_0 in H; auto); subst
        end
    end.

Lemma closed_rty_cap: forall τ (d1 d2 d3: aset) n,
    d1 ∩ d2 ⊆ d3 -> closed_rty n d1 τ -> closed_rty n d2 τ -> closed_rty n d3 τ.
Proof.
  induction τ; intros; invclear H0; invclear H1; mydestr; subst;
  constructor; auto; fast_set_solver.
Qed.

Lemma ok_dctx_single_implies_closed_rty: forall d x τ, ok_dctx d [(x, τ)] -> closed_rty 0 d τ.
Proof.
  intros. invclear H; auto.
Qed.

Lemma state_insert_subseteq_dom: forall (st: state) a v,
    dom aset st ⊆ dom aset (({a↦v}) st).
Proof.
  intros. destruct v; simpl; my_simplify_map_eq3.
  - destruct (st !! atom); my_simplify_map_eq3.
Qed.

Global Hint Resolve state_insert_subseteq_dom: core.

Lemma dom_subseteq_state_insert: forall (st: state) a v,
    dom aset (({a↦v}) st) ⊆ {[a]} ∪ dom aset st.
Proof.
  intros. destruct v; simpl; my_simplify_map_eq3.
  - destruct (st !! atom); my_simplify_map_eq3.
Qed.

Global Hint Resolve dom_subseteq_state_insert: core.

Ltac closed_rty_solver :=
  repeat match goal with
    | [H1: closed_rty ?n ?d1 ?τ, H2: closed_rty ?n ?d2 ?τ |- closed_rty ?n ?d3 ?τ ] =>
            apply (closed_rty_cap τ d1 d2 d3); auto; simpl; fast_set_solver
    | [H: closed_rty _ _ (-:{v: _ | _ | _ | _}⤑ ?τ) |- closed_rty _ _ ?τ] =>
        destruct H; mydestr; repeat split; auto
    | [H: valid_rty (-:{v: _ | _ | _ | _}⤑ ?τ) |- valid_rty ?τ] => invclear H; auto
    | [H: lc_rty_idx _ (-:{v: _ | _ | _ | _}⤑ ?τ) |- lc_rty_idx _ ?τ] => invclear H; auto
    | [H: closed_rty _ _ (-:{v: _ | _ | _ | ?ϕ}⤑ _) |- closed_rty _ _ {v: _ | _ | _ | ?ϕ}] =>
        destruct H; mydestr; repeat split; auto
    | [H: valid_rty (-:{v: _ | _ | _ | ?ϕ}⤑ _) |- valid_rty {v: _ | _ | _ | ?ϕ}] => invclear H; constructor; auto
    | [H: lc_rty_idx _ (-:{v: _ | _ | _ | ?ϕ}⤑ _) |- lc_rty_idx _ {v: _ | _ | _ | ?ϕ}] => invclear H; constructor; auto
    | [H: closed_rty _ _ (?τ1 ⤑ ?τ2) |- closed_rty _ _ ?τ1] =>
        destruct H; mydestr; repeat split; auto
    | [H: valid_rty (?τ1 ⤑ ?τ2) |- valid_rty ?τ1] => invclear H; auto
    | [H: lc_rty_idx _ (?τ1 ⤑ ?τ2) |- lc_rty_idx _ ?τ1] => invclear H; auto
    | [H: closed_rty _ _ (?τ1 ⤑ ?τ2) |- closed_rty _ _ ?τ2] =>
        destruct H; mydestr; repeat split; auto
    | [H: valid_rty (?τ1 ⤑ ?τ2) |- valid_rty ?τ2] => invclear H; auto
    | [H: lc_rty_idx _ (?τ1 ⤑ ?τ2) |- lc_rty_idx _ ?τ2] => invclear H; auto
    | [H: closed_rty ?n ?d1 ?τ |- closed_rty ?n ?d2 ?τ ] => apply (closed_rty_trans _ d1 d2); auto; fast_set_solver
    | [H: ok_dctx ?d [(_, ?τ)] |- closed_rty 0 ?d ?τ ] => apply ok_dctx_single_implies_closed_rty in H; auto
    | [|- rty_fv ?x ⊆ _ ] => refinement_simp1; my_set_solver; auto
    end.

Lemma ok_dctx_trans: forall Γ d1 d2,
    d1 ⊆ d2 -> ctxdom Γ ∩ d2 ≡ ∅ -> ok_dctx d1 Γ -> ok_dctx d2 Γ.
Proof.
  induction Γ; intros; auto; mydestr.
  - repeat constructor; fast_set_solver.
  - invclear H1.
    + constructor; eauto.
      closed_rty_solver. my_set_solver.
      apply (IHΓ ({[a]} ∪ d1) ({[a]} ∪ d2)); eauto; my_set_solver.
    + apply ok_dctx_cons_arr; auto.
      closed_rty_solver. my_set_solver.
      apply (IHΓ d1 d2); eauto; my_set_solver.
Qed.

Lemma ok_dctx_cap: forall Γ (d1 d2 d3: aset),
    d1 ∩ d2 ⊆ d3 -> ctxdom Γ ∩ d3 ≡ ∅ -> ok_dctx d1 Γ -> ok_dctx d2 Γ -> ok_dctx d3 Γ.
Proof.
  induction Γ; intros; invclear H1; invclear H2; mydestr; subst.
  - constructor.
  - constructor; auto. closed_rty_solver. my_set_solver.
    apply (IHΓ ({[x]} ∪ d1) ({[x]} ∪ d2)); auto.
    fast_set_solver. my_set_solver.
  - exfalso; auto.
  - exfalso; auto.
  - apply ok_dctx_cons_arr; auto. closed_rty_solver. my_set_solver.
    apply (IHΓ d1 d2); auto. my_set_solver.
Qed.

Ltac dec_solver2 :=
  repeat (simpl; (match goal with
                  | [H: ~ ?P |- context [decide ?P] ] => rewrite (decide_False _ _ H)
                  | [H: ?P |- context [decide ?P] ] => rewrite (decide_True _ _ H)
                  | [H: ~ ?P, H': context [decide ?P] |- _ ] => rewrite (decide_False _ _ H) in H'
                  | [H: ?P, H': context [decide ?P] |- _ ] => rewrite (decide_True _ _ H) in H'
                  end || (auto; var_dec_solver2))).

Lemma ctx_dom_rm_subseteq_ctx_dom: forall (Γ: listctx rty), ctxdom ⦑Γ⦒ ⊆ ctxdom Γ.
Proof.
  induction Γ; intros; mydestr; simpl; auto.
  dec_solver2; set_solver.
Qed.

Global Hint Resolve ctx_dom_rm_subseteq_ctx_dom: core.

Lemma notin_ctx_dom_implies_notin_ctx_dom_rm: forall x (Γ: listctx rty), x ∉ ctxdom Γ -> x ∉ ctxdom ⦑Γ⦒.
Proof.
  intros. pose (ctx_dom_rm_subseteq_ctx_dom Γ). set_solver.
Qed.

Global Hint Resolve notin_ctx_dom_implies_notin_ctx_dom_rm: core.

Lemma ok_ctx_implies_rm_ok_ctx: forall (Γ: listctx rty), ok Γ -> ok ⦑Γ⦒.
Proof.
  induction Γ; intros; mydestr; auto.
  rewrite ok_pre_destruct in H; mydestr.
  dec_solver2. rewrite ok_pre_destruct. split; auto.
Qed.

Global Hint Resolve ok_ctx_implies_rm_ok_ctx: core.

Lemma ok_dctx_implies_ctx_closed_rty:
  forall Γ d, ok_dctx d Γ -> ctx_closed_rty d Γ.
Proof.
  induction Γ; intros. intros Γ1 x τ_x Γ2 Hin. inversion Hin. auto_exfalso.
  invclear H.
  - assert (ok Γ) by (apply ok_dctx_regular in H7; mydestr; auto).
    apply IHΓ in H7. clear IHΓ. intros Γ1 a τ_a Γ2 Hin.
    destruct (atom_dec x a); subst; list_simplifier; dec_solver2.
    + rewrite <- (app_nil_l ((a, τ) :: Γ )) in Hin.
      apply ok_find_same in Hin; mydestr; subst; simpl. closed_rty_solver.
      listctx_set_solver.
    + apply (closed_rty_trans _ (ctxdom ⦑Γ1⦒ ∪ d)); try fast_set_solver;
      apply ok_find_neq_head in Hin; auto; mydestr; subst. dec_solver2.
      apply (closed_rty_trans _ (ctxdom ⦑x0⦒ ∪ ({[x]} ∪ d))); try fast_set_solver.
      eapply H7. list_simplifier; eauto.
      listctx_set_solver.
  - assert (ok Γ) by (apply ok_dctx_regular in H7; mydestr; auto).
    apply IHΓ in H7. clear IHΓ. intros Γ1 a τ_a Γ2 Hin.
    destruct (atom_dec x a); subst; list_simplifier.
    + rewrite <- (app_nil_l ((a, τ) :: Γ )) in Hin.
      apply ok_find_same in Hin; mydestr; subst. closed_rty_solver.
      listctx_set_solver.
    + apply (closed_rty_trans _ (ctxdom ⦑Γ1⦒ ∪ d)); try fast_set_solver.
      apply ok_find_neq_head in Hin; auto; mydestr; subst.
      apply (closed_rty_trans _ (ctxdom ⦑x0⦒ ∪ d)); try fast_set_solver. dec_solver2.
      eapply H7. list_simplifier; reflexivity.
      listctx_set_solver.
Qed.

Lemma ok_dctx_regular2: forall d Γ,
    ok_dctx d Γ -> ctx_closed_rty d Γ /\ ok Γ /\ (ctxdom Γ ∩ d ≡ ∅).
Proof.
  intros. split.
  - apply ok_dctx_implies_ctx_closed_rty; auto.
  - apply ok_dctx_regular; auto.
Qed.

Lemma ok_dctx_shift: forall d a r Γ,
    ok_dctx d ((a, r) :: Γ) -> ok_dctx ({[a]} ∪ d) Γ.
Proof.
  intros.
  assert (({[a]} ∪ ctxdom Γ) ∩ d ≡ ∅). { apply ok_dctx_regular2 in H; mydestr. fast_set_solver. }
  invclear H; auto. apply ok_dctx_trans with (d1:=d); eauto. fast_set_solver. set_solver.
Qed.

Ltac ok_dctx_solver1 :=
  match goal with
  | [H1: ok_dctx ?d1 ?τ, H2: ok_dctx ?d2 ?τ |- ok_dctx ?d3 ?τ ] =>
            apply (ok_dctx_cap τ d1 d2 d3); auto; simpl; fast_set_solver
  | [H: ok_dctx _ _ |- ok _ ] => apply ok_dctx_regular2 in H; mydestr; auto
  | [H: ok_dctx _ _ |- _ ≡ _ ] => apply ok_dctx_regular2 in H; mydestr; auto
  | [H: ok_dctx ?d1 ?τ |- ok_dctx ?d2 ?τ ] =>
      apply (ok_dctx_trans τ d1 d2); simpl; auto; fast_set_solver
  | [H: ok_dctx _ ((_, _) :: ?Γ) |- ok_dctx _ ?Γ] => apply ok_dctx_shift
  end || listctx_set_solver.

Fixpoint ctxdom_base (Γ: listctx rty) : aset :=
  match Γ with
  | [] => ∅
  | (x, {v: _ | _ | _ | _ }) :: Γ => {[x]} ∪ ctxdom_base Γ
  | (x, [v: _ | _ | _ | _ ]) :: Γ => {[x]} ∪ ctxdom_base Γ
  | (x, _) :: Γ => ctxdom_base Γ
  end.

Lemma ok_dctx_post_destruct: forall Γ d x τ,
    ok_dctx d (Γ ++ [(x, τ)]) <->
      ok_dctx d Γ /\ x ∉ d /\ x ∉ ctxdom Γ /\ closed_rty 0 (ctxdom ⦑ Γ ⦒ ∪ d) τ.
Proof.
  induction Γ; simpl; split; intros; mydestr.
  - invclear H; do 3 (constructor; auto); closed_rty_solver.
  - destruct (classic (is_arr τ)).
    + apply ok_dctx_cons_arr; auto; closed_rty_solver.
    + apply ok_dctx_cons_base; auto; closed_rty_solver. constructor.
  - invclear H.
    + apply IHΓ in H8; mydestr. do 3 (constructor; auto; try listctx_set_solver).
      destruct r; closed_rty_solver.
    + apply IHΓ in H8; mydestr. do 3 (constructor; auto; try listctx_set_solver).
      destruct r; invclear H3; closed_rty_solver.
  - invclear H.
    + apply ok_dctx_cons_base; auto; try listctx_set_solver.
      rewrite IHΓ. do 3 (split; auto; try fast_set_solver).
      destruct r; closed_rty_solver.
    + apply ok_dctx_cons_arr; auto; try listctx_set_solver.
      rewrite IHΓ. do 3 (split; auto; try fast_set_solver).
      destruct r; invclear H6; closed_rty_solver.
Qed.

Ltac ok_dctx_solver2 :=
  match goal with
      | [H: ok_dctx ?d ((?a, ?b) :: ?l ++ [_]) |- ok_dctx ?d ((?a, ?b) :: ?l)] =>
          rewrite app_comm_cons in H; rewrite ok_dctx_post_destruct in H; mydestr; auto
  end || ok_dctx_solver1.

Ltac ok_dctx_solver := ok_dctx_solver2.

Ltac refinement_set_simp :=
  repeat
    match goal with
    | [H: ok_dctx _ _ |- _ ≡ _ ] => apply ok_dctx_regular2 in H; mydestr
    | [H: ok ((_, _) :: _) |- _ ≡ _ ] => rewrite ok_pre_destruct in H; mydestr
    | [H: ok_dctx _ _ |- _ ⊆ _ ] => apply ok_dctx_regular2 in H; mydestr
    | [H: ok ((_, _) :: _) |- _ ⊆ _ ] => rewrite ok_pre_destruct in H; mydestr
    end.

Lemma ctx_erase_perserve_ctxdom: forall Γ, ctxdom ⌊ Γ ⌋* = ctxdom Γ.
Proof.
  induction Γ; simpl; auto.
  mydestr; simpl. rewrite IHΓ. auto.
Qed.

Ltac ctx_erase_simp1:=
  repeat match goal with
  | [H: context [ctxdom ⌊ ?Γ ⌋*] |- _ ] =>
      setoid_rewrite (ctx_erase_perserve_ctxdom Γ) in H
  | [ |- context [ctxdom ⌊ ?Γ ⌋*]] =>
      setoid_rewrite (ctx_erase_perserve_ctxdom Γ)
  end || listctx_set_simpl; simpl.

Lemma ctx_erase_commute_okapp: forall Γ1 Γ2, ok ⌊ Γ1 ++ Γ2 ⌋* <-> ok ( ⌊ Γ1 ⌋* ++  ⌊ Γ2 ⌋*).
Proof.
  split; induction Γ1; simpl; listctx_set_simpl; intros; simpl; auto.
  - rewrite ok_pre_destruct. rewrite ok_pre_destruct in H. mydestr.
    split; auto. simpl in H0. ctx_erase_simp1.
  - rewrite ok_pre_destruct. rewrite ok_pre_destruct in H. mydestr.
    split; auto. simpl in H0. ctx_erase_simp1.
Qed.

Ltac ctx_erase_simp2:=
  repeat match goal with
    | [H: context [ctxdom ⌊ ?Γ ⌋*] |- _ ] =>
        setoid_rewrite (ctx_erase_perserve_ctxdom Γ) in H
    | [ |- context [ctxdom ⌊ ?Γ ⌋*]] =>
        setoid_rewrite (ctx_erase_perserve_ctxdom Γ)
    | [H: context [ ⌊ ?a ++ ?b ⌋* ] |- _ ] => rewrite (ctx_erase_commute_okapp a b) in H
    | [ |- context [ ⌊ ?a ++ ?b ⌋* ] ] => rewrite (ctx_erase_commute_okapp a b)
    end || listctx_set_simpl; simpl.

Lemma ctx_erase_perserve_ok: forall Γ, ok Γ <-> ok ⌊ Γ ⌋*.
Proof.
  split; intros.
  - induction H; simpl; auto. ctx_erase_simp2.
    constructor; auto. ctx_erase_simp2.
  - induction Γ; simpl; auto. mydestr. simpl in H.
    rewrite ok_pre_destruct in H. mydestr. ctx_erase_simp2.
    rewrite ok_pre_destruct. constructor; auto.
Qed.

Lemma ctx_erase_commute_app: forall Γ1 Γ2, ⌊ Γ1 ++ Γ2 ⌋* = ⌊ Γ1 ⌋* ++  ⌊ Γ2 ⌋*.
Proof.
  induction Γ1; simpl; listctx_set_simpl; intros; simpl; auto.
  rewrite IHΓ1; auto.
Qed.

Ltac ctx_erase_simp3:=
  repeat match goal with
    | [H: context [ctxdom ⌊ ?Γ ⌋*] |- _ ] =>
        setoid_rewrite (ctx_erase_perserve_ctxdom Γ) in H
    | [ |- context [ctxdom ⌊ ?Γ ⌋*]] =>
        setoid_rewrite (ctx_erase_perserve_ctxdom Γ)
    | [H: context [ ⌊ ?a ++ ?b ⌋* ] |- _ ] => setoid_rewrite (ctx_erase_commute_app a b) in H
    | [ |- context [ ⌊ ?a ++ ?b ⌋* ] ] => setoid_rewrite (ctx_erase_commute_app a b)
    | [H: context [ ok ⌊ ?a ⌋* ] |- _ ] => setoid_rewrite <- (ctx_erase_perserve_ok a) in H
    | [ |- context [ ok ⌊ ?a ⌋* ] ] => setoid_rewrite <- (ctx_erase_perserve_ok a)
    end || listctx_set_simpl; simpl.

Lemma subst_perserve_erase: forall τ z c, ⌊({z:=c}r) τ⌋ = ⌊τ⌋.
Proof.
  induction τ; intros; destruct c; simpl; eauto; try (rewrite IHτ; auto);
  try (rewrite IHτ1; rewrite IHτ2; auto).
Qed.

Ltac ctx_erase_simp4:=
  repeat ((match goal with
           | [H: context [⌊({_:=_}r) _⌋] |- _ ] => setoid_rewrite subst_perserve_erase in H
           | [|- context [⌊({_:=_}r) _⌋] ] => setoid_rewrite subst_perserve_erase
           end; auto) || ctx_erase_simp3).

Ltac ctx_erase_simp5 :=
        repeat (match goal with
             | [H: ok_dctx _ _ |- ok _] => apply ok_dctx_regular in H; mydestr
             | [H: ok ?a |- ok ?b] =>
                 match type of b with
                 | (list (atom * ty)) =>
                     match type of a with
                     | (list (atom * rty)) =>
                         rewrite ctx_erase_perserve_ok in H; simpl in H
                     end
                 end
             end); ctx_erase_simp4.

Ltac ctx_erase_simp:= ctx_erase_simp5.

Lemma state_subst_implies_r_susbt_eq: forall k (a: atom) ϕ bst st (c_x: constant) v,
    refinement_open k a ϕ bst (<[a:=c_x]> st) v <-> refinement_open k c_x ϕ bst (<[a:=c_x]> st) v.
Proof.
  unfold refinement_open; split; intros; my_simplify_map_eq3.
Qed.
