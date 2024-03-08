From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import RefinementType.
From CT Require Import Denotation.
From CT Require Import Instantiation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Trace.
Import ListCtx.
Import RefinementType.

(** This file proves auxiliary lemmas about multi-substitution and provides
  handy tactics. *)

Lemma closed_env_insert env x v :
  env !! x = None ->
  closed_env (<[x:=v]>env) ->
  closed_value v /\ closed_env env.
Proof.
  intro.
  unfold closed_env.
  rewrite map_Forall_insert; eauto.
Qed.

Ltac apply_msubst_ind :=
  unfold msubst;
  match goal with
  | |- ?T =>
      match T with
      | context [map_fold ?a ?b ?m] =>
          match eval pattern (map_fold a b m) in T with
          | ?P _ =>
              match eval pattern m in P with
              | ?P _ =>
                  let P := eval simpl in (fun r m => P m r) in
                    apply (map_fold_ind P)
              end
          end
      end
  end.

Ltac gen_closed_env :=
  repeat
    match goal with
    | H : closed_env (<[?i:=_]> ?m), H' : ?m !! ?i = None |- _ =>
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        destruct (closed_env_insert _ _ _ H' H) as [H1 H2];
        uniq_hyp H1; uniq_hyp H2
    | H : closed_env ?m, H' : ?m !! _ = Some ?v |- _ =>
        let T := fresh "H" in
        assert (closed_value v) as T by eauto;
        uniq_hyp T
    (* | H : ctxRst _ ?env |- _ => *)
    (*     let T := fresh "H" in *)
    (*     assert (closed_env env) as T by eauto using ctxRst_closed_env; *)
    (*     uniq_hyp T *)
    end.

Lemma msubst_insert {T: Type}
  (f_subst: atom -> value -> T -> T)
  (subst_commute: forall x u_x y u_y e,
      x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
      f_subst x u_x (f_subst y u_y e) =
        f_subst y u_y (f_subst x u_x e))
  :
  forall (Γv: env) (x: atom) (v_x: value) (e: T),
    closed_env Γv ->
    closed_value v_x ->
    Γv !! x = None ->
    msubst f_subst (<[x:=v_x]> Γv) e = f_subst x v_x (msubst f_subst Γv e).
Proof.
  intros.
  apply map_fold_insert_L; eauto.
  intros.
  assert (closed_env (<[x:=v_x]>Γv)). {
    apply map_Forall_insert; eauto.
  }
  gen_closed_env.
  apply subst_commute; eauto; my_set_solver.
Qed.

Ltac msubst_tac :=
  intros *; apply_msubst_ind; intros; subst; simpl; eauto;
  gen_closed_env; simp_hyps; subst.

Ltac fold_msubst := change (map_fold ?s ?e ?m) with (msubst s m e) in *.

Ltac rewrite_msubst_insert :=
  cbn; fold_msubst; rewrite !msubst_insert;
  eauto using subst_commute_value, subst_commute_tm, subst_commute_qualifier,
    subst_commute_pty, subst_commute_am, subst_commute_hty.

Lemma pty_erase_msubst_eq ρ Γv :
  pty_erase ρ = pty_erase (m{Γv}p ρ).
Proof.
  msubst_tac.
  qauto using pty_erase_subst_eq.
Qed.

Lemma hty_erase_msubst_eq τ Γv :
  hty_erase τ = hty_erase (m{Γv}h τ).
Proof.
  msubst_tac.
  qauto using hty_erase_subst_eq.
Qed.

Lemma msubst_qualifier: forall Γv ϕ,
    closed_env Γv ->
    (m{Γv}q) ϕ =
      match ϕ with
      | qual vals prop =>
          qual (vmap (m{Γv}v) vals) prop
      end.
Proof.
  msubst_tac.
  - destruct ϕ.
    f_equal.
    erewrite Vector.map_ext.
    by rewrite Vector.map_id.
    intros. simpl.
    by rewrite map_fold_empty.
  - destruct ϕ. simpl. f_equal.
    rewrite Vector.map_map.
    apply Vector.map_ext.
    intros; rewrite_msubst_insert.
Qed.

Lemma msubst_qualifier_and Γv q1 q2 :
  closed_env Γv ->
  m{Γv}q (q1 & q2) = (m{Γv}q q1) & (m{Γv}q q2).
Proof.
  msubst_tac.
  rewrite_msubst_insert.
  apply qualifier_and_subst.
Qed.

Lemma msubst_aany: forall (Γv: env),
    m{Γv}a aany = aany.
Proof.
  msubst_tac.
Qed.

Lemma msubst_aconcat: forall (Γv: env) A1 A2,
    closed_env Γv ->
    m{Γv}a (aconcat A1 A2) = (aconcat (m{Γv}a A1) (m{Γv}a A2)).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_aevent: forall (Γv: env) op ϕ,
    closed_env Γv ->
    m{Γv}a ⟨op|ϕ⟩ = ⟨op| m{Γv}q ϕ⟩.
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_constant: forall Γv (c: constant), (m{Γv}v) c = c.
Proof.
  msubst_tac.
Qed.

Lemma msubst_bvar: forall Γv n, (m{Γv}v) (vbvar n) = vbvar n.
Proof.
  msubst_tac.
Qed.

Lemma msubst_fvar: forall Γv (x : atom),
    closed_env Γv ->
    (m{Γv}v) x = match Γv !! x with
                 | Some v => v
                 | None => x
                 end.
Proof.
  msubst_tac.
  destruct (decide (x = i)); subst; simplify_map_eq. reflexivity.
  case_match.
  apply subst_fresh_value.
  gen_closed_env. my_set_solver.
  simpl. rewrite decide_False; eauto.
Qed.

Lemma msubst_lam: forall Γv T e,
    closed_env Γv ->
    ((m{Γv}v) (vlam T e)) = (vlam T ((m{Γv}t) e)).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_fix: forall Γv T e,
    closed_env Γv ->
    ((m{Γv}v) (vfix T e)) = (vfix T ((m{Γv}t) e)).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_value: forall Γv (v:value),
    closed_env Γv ->
    (m{Γv}t) (treturn v) = (m{Γv}v) v.
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_match: forall Γv (v: value) e1 e2,
    closed_env Γv ->
    ((m{Γv}t) (tmatchb v e1 e2)) = tmatchb (m{Γv}v v) (m{Γv}t e1) (m{Γv}t e2).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_lete: forall (Γv: env) e_x e,
    closed_env Γv ->
    (m{Γv}t (tlete e_x e) = tlete ((m{Γv}t) e_x) ((m{Γv}t) e)).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_tleteffop: forall Γv op (v2: value) e,
    closed_env Γv ->
    (m{Γv}t) (tleteffop op v2 e) = (tleteffop op (m{Γv}v v2) (m{Γv}t e)).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_tletapp: forall Γv (v1 v2: value) e,
    closed_env Γv ->
    (m{Γv}t) (tletapp v1 v2 e) = (tletapp (m{Γv}v v1) (m{Γv}v v2) (m{Γv}t e)).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_basepty: forall Γv b ϕ,
    closed_env Γv ->
    (m{Γv}p) {:b|ϕ} = {:b| (m{Γv}q) ϕ}.
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_arrpty: forall Γv ρ τ,
    closed_env Γv ->
    ((m{Γv}p) (ρ⇨τ)) = ((m{Γv}p ρ)⇨(m{Γv}h τ)).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_ghostpty: forall Γv b ρ,
    closed_env Γv ->
    ((m{Γv}p) (b⇢ρ)) = (b⇢(m{Γv}p ρ)).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_hoarehty: forall (Γv: env) ρ A B,
    closed_env Γv ->
    m{Γv}h (<[ A ] ρ [ B ]>) = <[ m{Γv}a A ] (m{Γv}p ρ) [ m{Γv}a B ]>.
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_interhty: forall (Γv: env) τ1 τ2,
    closed_env Γv ->
    m{Γv}h (τ1 ⊓ τ2) = (m{Γv}h τ1) ⊓ (m{Γv}h τ2).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Tactic Notation "rewrite_msubst" constr(lem) "in" hyp(H) :=
  rewrite lem in H; eauto using ctxRst_closed_env.

Tactic Notation "rewrite_msubst" constr(lem) :=
  rewrite lem in *; eauto using ctxRst_closed_env.

Lemma msubst_mk_top: forall (Γv: env) b,
    closed_env Γv ->
    m{Γv}p (mk_top b) = mk_top b.
Proof.
  intros.
  unfold mk_top, mk_q_under_top.
  rewrite_msubst msubst_basepty.
  rewrite_msubst msubst_qualifier.
Qed.

Lemma msubst_mk_eq_constant: forall (Γv: env) c,
    closed_env Γv ->
    (m{Γv}p) (mk_eq_constant c) = (mk_eq_constant c).
Proof.
  intros.
  unfold mk_eq_constant, mk_q_bvar_eq_val.
  repeat rewrite_msubst msubst_basepty.
  repeat rewrite_msubst msubst_qualifier.
  simpl.
  repeat rewrite_msubst msubst_bvar.
  repeat rewrite_msubst msubst_constant.
Qed.

Lemma msubst_mk_eq_var: forall (Γv: env) b x v,
    closed_env Γv ->
    Γv !! x = Some v ->
    (m{Γv}p) (mk_eq_var b x) = {:b | b0:v= v}.
Proof.
  intros.
  unfold mk_eq_var.
  repeat rewrite_msubst msubst_basepty.
  repeat rewrite_msubst msubst_qualifier.
  simpl.
  repeat rewrite_msubst msubst_bvar.
  repeat rewrite_msubst msubst_fvar.
  rewrite H0.
  eauto.
Qed.

Ltac msubst_simp :=
  match goal with
  | H: context [ m{ _ }a (aany) ] |- _ => rewrite msubst_aany in H
  | |- context [ m{ _ }a (aany) ] => rewrite msubst_aany
  | H: context [ m{ _ }a (aconcat _ _) ] |- _ => rewrite msubst_aconcat in H
  | |- context [ m{ _ }a (aconcat _ _) ] => rewrite msubst_aconcat
  | H: context [ m{ _ }a (aevent _ _) ] |- _ => rewrite msubst_aevent in H
  | |- context [ m{ _ }a (aevent _ _) ] => rewrite msubst_aevent
  | H: context [ m{ _ }t (tlete _ _) ] |- _ => rewrite msubst_lete in H
  | |- context [ m{ _ }t (tlete _ _) ] => rewrite msubst_lete
  | H: context [ m{ _ }t (tleteffop _ _ _) ] |- _ => rewrite msubst_tleteffop in H
  | |- context [ m{ _ }t (tleteffop _ _ _) ] => rewrite msubst_tleteffop
  | H: context [ m{ _ }t (tletapp _ _ _) ] |- _ => rewrite msubst_tletapp in H
  | |- context [ m{ _ }t (tletapp _ _ _) ] => rewrite msubst_tletapp
  | H: context [ m{ _ }v (vfix _ _) ] |- _ => rewrite msubst_fix in H
  | |- context [ m{ _ }v (vfix _ _) ] => rewrite msubst_fix
  | H: context [ m{ _ }t (treturn _) ] |- _ => rewrite msubst_value in H
  | |- context [ m{ _ }t (treturn _) ] => rewrite msubst_value
  | H: context [ m{ _ }v (vlam _ _) ] |- _ => rewrite msubst_lam in H
  | |- context [ m{ _ }v (vlam _ _) ] => rewrite msubst_lam
  | H: context [ m{ _ }t (tmatchb _ _ _) ] |- _ => rewrite msubst_match in H
  | |- context [ m{ _ }t (tmatchb _ _ _) ] => rewrite msubst_match
  | H: context [ m{ _ }v (vbvar _) ] |- _ => rewrite msubst_bvar in H
  | |- context [ m{ _ }v (vbvar _) ] => rewrite msubst_bvar
  | H: context [ m{ _ }v (vfvar _) ] |- _ => rewrite msubst_fvar in H
  | |- context [ m{ _ }v (vfvar _) ] => rewrite msubst_fvar
  | H: context [ m{ _ }v (vconst _) ] |- _ => rewrite msubst_constant in H
  | |- context [ m{ _ }v (vconst _) ] => rewrite msubst_constant
  (* | H: context [ m{ _ }q _ ] |- _ => rewrite msubst_qualifier in H *)
  (* | |- context [ m{ _ }q _ ] => rewrite msubst_qualifier *)
  | H: context [ m{ _ }q (_ & _) ] |- _ => rewrite msubst_qualifier_and in H
  | |- context [ m{ _ }q (_ & _) ] => rewrite msubst_qualifier_and
  | H: context [ m{ _ }p {: _ | _ } ] |- _ => rewrite msubst_basepty in H
  | |- context [ m{ _ }p {: _ | _ } ] => rewrite msubst_basepty
  | H: context [ m{ _ }p (_ ⇨ _) ] |- _ => rewrite msubst_arrpty in H
  | |- context [ m{ _ }p (_ ⇨ _) ] => rewrite msubst_arrpty
  | H: context [ m{ _ }p (_ ⇢ _) ] |- _ => rewrite msubst_ghostpty in H
  | |- context [ m{ _ }p (_ ⇢ _) ] => rewrite msubst_ghostpty
  | H: context [ m{ _ }h (<[_] _ [_]>) ] |- _ => rewrite msubst_hoarehty in H
  | |- context [ m{ _ }h <[_] _ [_]> ] => rewrite msubst_hoarehty
  | H: context [ m{ _ }h (_⊓_) ] |- _ => rewrite msubst_interhty in H
  | |- context [ m{ _ }h (_⊓_) ] => rewrite msubst_interhty
  | H: context [ m{ _ }p (mk_top _) ] |- _ => rewrite msubst_mk_top in H
  | |- context [ m{ _ }p (mk_top _) ] => rewrite msubst_mk_top
  | H: context [ m{ _ }p (mk_eq_constant _) ] |- _ => rewrite msubst_mk_eq_constant in H
  | |- context [ m{ _ }p (mk_eq_constant _) ] => rewrite msubst_mk_eq_constant
  | H: context [ m{ _ }p (mk_eq_var _ ?x) ], H': _ !! ?x = Some ?v |- _ => rewrite msubst_mk_eq_var with (v:=v) in H
  | H': _ !! ?x = Some ?v |- context [ m{ _ }p (mk_eq_var _ ?x) ] => rewrite msubst_mk_eq_var with (v:=v)
  end; eauto using ctxRst_closed_env.

(* Most lemmas here are generalization of the corresponding lemmas about
single-substitution. *)

Lemma msubst_open_var_tm: forall (Γv: env) e k (x: atom),
    closed_env Γv ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ->
    (m{Γv}t) ({k ~t> x} e) = {k ~t> x} ((m{Γv}t) e).
Proof.
  msubst_tac.
  rewrite_msubst_insert.
  apply map_Forall_insert in H2; eauto.
  rewrite H6; eauto.
  apply subst_open_var_tm. my_set_solver.
  qauto. qauto.
  my_set_solver.
Qed.

Lemma msubst_open_am: forall (Γv: env) (a: am) k (v_x: value),
    closed_env Γv ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    (m{Γv}a) ({k ~a> v_x} a) = {k ~a> (m{Γv}v v_x)} (m{Γv}a a).
Proof.
  msubst_tac.
  rewrite_msubst_insert.
  apply map_Forall_insert in H2; eauto. simp_hyps.
  subst.
  by apply subst_open_am.
Qed.

Lemma msubst_open_pty: forall (Γv: env) (ρ: pty) k (v_x: value),
    closed_env Γv ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    (m{Γv}p) ({k ~p> v_x} ρ) = {k ~p> (m{Γv}v v_x)} (m{Γv}p ρ).
Proof.
  msubst_tac.
  rewrite_msubst_insert.
  apply map_Forall_insert in H2; eauto. simp_hyps.
  subst.
  by apply subst_open_pty.
Qed.

Lemma msubst_open_hty: forall (Γv: env) (τ: hty) k (v_x: value),
    closed_env Γv ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    (m{Γv}h) ({k ~h> v_x} τ) = {k ~h> (m{Γv}v v_x)} (m{Γv}h τ).
Proof.
  msubst_tac.
  rewrite_msubst_insert.
  apply map_Forall_insert in H2; eauto. simp_hyps.
  subst.
  by apply subst_open_hty.
Qed.

Lemma msubst_fresh_qualifier Γv ϕ :
  dom Γv ## qualifier_fv ϕ ->
  (m{Γv}q) ϕ = ϕ.
Proof.
  msubst_tac.
  rewrite H0.
  apply subst_fresh_qualifier.
  my_set_solver.
  my_set_solver.
Qed.

Lemma msubst_fresh_pty Γv ρ :
  dom Γv ## pty_fv ρ ->
  (m{Γv}p) ρ = ρ.
Proof.
  msubst_tac.
  rewrite H0.
  apply subst_fresh_pty.
  my_set_solver.
  my_set_solver.
Qed.

Lemma msubst_fresh_am Γv a :
  dom Γv ## am_fv a ->
  (m{Γv}a) a = a.
Proof.
  msubst_tac.
  rewrite H0.
  apply subst_fresh_am.
  my_set_solver.
  my_set_solver.
Qed.

Lemma msubst_fresh_value Γv v :
  dom Γv ## fv_value v ->
  (m{Γv}v) v = v.
Proof.
  msubst_tac.
  rewrite H0.
  apply subst_fresh_value.
  my_set_solver.
  my_set_solver.
Qed.

(* The proof can be reduced to [msubst_open_var_tm] and [msubst_fresh_tm]
(haven't defined yet; see [msubst_fresh_pty] for example). It's a pain to define
those for every [msubst_intro_*]. Don't bother yet. *)
Lemma msubst_intro_tm: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~t> v_x} ((m{Γv}t) e) = (m{<[x:=v_x]> Γv}t) ({k ~t> x} e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
  msubst_tac.
  rewrite map_fold_empty. rewrite open_subst_same_tm. auto. my_set_solver.
  rewrite_msubst_insert.
  apply map_Forall_insert in H3; eauto.
  rewrite subst_commute_tm by my_set_solver.
  rewrite <- H0 by my_set_solver.
  by rewrite subst_open_tm_closed by qauto.
Qed.

Lemma msubst_intro_value: forall (Γv: env) (v: value) k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale v ->
    {k ~v> v_x} ((m{Γv}v) v) = (m{<[x:=v_x]> Γv}v) ({k ~v> x} v).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
  msubst_tac.
  rewrite map_fold_empty. rewrite open_subst_same_value. auto. my_set_solver.
  rewrite_msubst_insert.
  apply map_Forall_insert in H3; eauto.
  rewrite subst_commute_value by my_set_solver.
  rewrite <- H0 by my_set_solver.
  by rewrite subst_open_value_closed by qauto.
Qed.

Lemma msubst_intro_hty: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~h> v_x} ((m{Γv}h) e) = (m{<[x:=v_x]> Γv}h) ({k ~h> x} e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
  msubst_tac.
  rewrite map_fold_empty.
  rewrite open_subst_same_hty. auto. my_set_solver.
  rewrite_msubst_insert.
  apply map_Forall_insert in H3; eauto.
  rewrite subst_commute_hty by my_set_solver.
  rewrite <- H0 by my_set_solver.
  by rewrite subst_open_hty_closed by qauto.
Qed.

Lemma msubst_intro_pty: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~p> v_x} ((m{Γv}p) e) = (m{<[x:=v_x]> Γv}p) ({k ~p> x} e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
  msubst_tac.
  rewrite map_fold_empty.
  rewrite open_subst_same_pty. auto. my_set_solver.
  rewrite_msubst_insert.
  apply map_Forall_insert in H3; eauto.
  rewrite subst_commute_pty by my_set_solver.
  rewrite <- H0 by my_set_solver.
  by rewrite subst_open_pty_closed by qauto.
Qed.

Lemma msubst_intro_qualifier: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~q> v_x} ((m{Γv}q) e) = (m{<[x:=v_x]> Γv}q) ({k ~q> x} e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
  msubst_tac.
  rewrite map_fold_empty. rewrite open_subst_same_qualifier. auto. my_set_solver.
  rewrite_msubst_insert.
  apply map_Forall_insert in H3; eauto.
  rewrite subst_commute_qualifier by my_set_solver.
  rewrite <- H0 by my_set_solver.
  by rewrite subst_open_qualifier_closed by qauto.
Qed.

Lemma msubst_intro_am: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~a> v_x} ((m{Γv}a) e) = (m{<[x:=v_x]> Γv}a) ({k ~a> x} e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
  msubst_tac.
  rewrite map_fold_empty.
  rewrite open_subst_same_am. auto. my_set_solver.
  rewrite_msubst_insert.
  apply map_Forall_insert in H3; eauto.
  rewrite subst_commute_am by my_set_solver.
  rewrite <- H0 by my_set_solver.
  by rewrite subst_open_am_closed by qauto.
Qed.

Lemma msubst_pty_fv_subseteq Γv v_x ρ:
  closed_env Γv ->
  closed_value v_x ->
  pty_fv (m{Γv}p ρ) ⊆ pty_fv ρ.
Proof.
  msubst_tac.
  rewrite fv_of_subst_pty_closed by eauto. my_set_solver.
Qed.

Lemma msubst_hty_fv_subseteq Γv v_x τ:
  closed_env Γv ->
  closed_value v_x ->
  hty_fv (m{Γv}h τ) ⊆ hty_fv τ.
Proof.
  msubst_tac.
  rewrite fv_of_subst_hty_closed by eauto. my_set_solver.
Qed.

Lemma msubst_qualifier_fv_subseteq Γv v_x ϕ:
  closed_env Γv ->
  closed_value v_x ->
  qualifier_fv (m{Γv}q ϕ) ⊆ qualifier_fv ϕ.
Proof.
  msubst_tac.
  rewrite fv_of_subst_qualifier_closed by eauto. my_set_solver.
Qed.

Lemma msubst_am_fv_subseteq Γv v_x a:
  closed_env Γv ->
  closed_value v_x ->
  am_fv (m{Γv}a a) ⊆ am_fv a.
Proof.
  msubst_tac.
  rewrite fv_of_subst_am_closed by eauto. my_set_solver.
Qed.

Lemma msubst_tm_fv_subseteq Γv v_x t:
  closed_env Γv ->
  closed_value v_x ->
  fv_tm (m{Γv}t t) ⊆ fv_tm t.
Proof.
  msubst_tac.
  rewrite fv_of_subst_tm by eauto. my_set_solver.
Qed.

Lemma msubst_value_fv_subseteq Γv v_x (v : value):
  closed_env Γv ->
  closed_value v_x ->
  fv_value (m{Γv}v v) ⊆ fv_tm v.
Proof.
  msubst_tac.
  rewrite fv_of_subst_value by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_pty Γv x v_x ρ:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ pty_fv ρ ->
  (m{<[x:=v_x]> Γv}p) ρ = (m{Γv}p) ρ.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_pty.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_pty_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_hty Γv x v_x τ:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ hty_fv τ ->
  (m{<[x:=v_x]> Γv}h) τ = (m{Γv}h) τ.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_hty.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_hty_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_qualifier Γv x v_x ϕ:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ qualifier_fv ϕ ->
  (m{<[x:=v_x]> Γv}q) ϕ = (m{Γv}q) ϕ.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_qualifier.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_qualifier_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_am Γv x v_x a:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ am_fv a ->
  (m{<[x:=v_x]> Γv}a) a = (m{Γv}a) a.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_am.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_am_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_tm Γv x v_x t:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ fv_tm t ->
  (m{<[x:=v_x]> Γv}t) t = (m{Γv}t) t.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_tm.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_tm_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_value Γv x v_x (v : value):
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ fv_tm v ->
  (m{<[x:=v_x]> Γv}v) v = (m{Γv}v) v.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_value.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_value_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma lc_msubst_pty Γv (ρ: pty):
  lc_pty (m{Γv}p ρ) ->
  map_Forall (fun _ v => lc (treturn v)) Γv ->
  lc_pty ρ.
Proof.
  msubst_tac.
  apply map_Forall_insert in H2; eauto. simp_hyps.
  eauto using lc_subst_pty.
Qed.

Lemma msubst_lc_pty Γv (ρ: pty):
  lc_pty ρ ->
  map_Forall (fun _ v => lc (treturn v)) Γv ->
  lc_pty (m{Γv}p ρ).
Proof.
  msubst_tac.
  apply map_Forall_insert in H2; eauto. simp_hyps.
  eauto using subst_lc_pty.
Qed.

Lemma lc_msubst_hty Γv (τ: hty):
  lc_hty (m{Γv}h τ) ->
  map_Forall (fun _ v => lc (treturn v)) Γv ->
  lc_hty τ.
Proof.
  msubst_tac.
  apply map_Forall_insert in H2; eauto. simp_hyps.
  eauto using lc_subst_hty.
Qed.

Lemma msubst_lc_hty Γv (τ: hty):
  lc_hty τ ->
  map_Forall (fun _ v => lc (treturn v)) Γv ->
  lc_hty (m{Γv}h τ).
Proof.
  msubst_tac.
  apply map_Forall_insert in H2; eauto. simp_hyps.
  eauto using subst_lc_hty.
Qed.

Lemma am_denotation_fv: forall Γv x v_x A,
    closed_env Γv ->
    closed_value v_x ->
    x ∉ dom Γv ->
    forall α,
      a⟦(m{Γv}a) A⟧ α -> a⟦(m{<[x:=v_x]> Γv}a) A⟧ α.
Proof.
  intros. rewrite_msubst_insert.
  rewrite subst_fresh_am. auto.
  select (a⟦_⟧ _) (fun H => apply langA_closed in H).
  simp_hyps. select (closed_am _ _) (fun H => sinvert H). my_set_solver.
  apply not_elem_of_dom. eauto.
Qed.

Lemma ptyR_msubst_insert_eq Γv ρ v x u :
  closed_env Γv ->
  closed_value u ->
  Γv !! x = None ->
  (p⟦(m{ Γv }p) ρ⟧) v ->
  (p⟦(m{ <[x:=u]> Γv }p) ρ⟧) v.
Proof.
  intros. rewrite_msubst_insert.
  rewrite subst_fresh_pty. auto.
  select (p⟦_⟧ _) (fun H => apply ptyR_typed_closed in H).
  simp_hyps. select (closed_pty _ _) (fun H => sinvert H). my_set_solver.
Qed.

Lemma fv_of_msubst_pty_closed Γv ρ:
  closed_env Γv ->
  pty_fv (m{Γv}p ρ) = pty_fv ρ ∖ dom Γv.
Proof.
  revert Γv.
  msubst_tac. my_set_solver.
  rewrite fv_of_subst_pty_closed by eauto.
  rewrite dom_insert_L. my_set_solver.
Qed.

Lemma fv_of_msubst_hty_closed Γv τ:
  closed_env Γv ->
  hty_fv (m{Γv}h τ) = hty_fv τ ∖ dom Γv.
Proof.
  revert Γv.
  msubst_tac. my_set_solver.
  rewrite fv_of_subst_hty_closed by eauto.
  rewrite dom_insert_L. my_set_solver.
Qed.

Lemma msubst_preserves_closed_pty Γ Γv Γ' ρ :
  ctxRst Γ Γv ->
  closed_pty (ctxdom (Γ ++ Γ')) ρ ->
  closed_pty (ctxdom (Γ')) (m{Γv}p ρ).
Proof.
  intros HΓv H.
  sinvert H.
  econstructor. eauto using msubst_lc_pty, ctxRst_lc.
  rewrite fv_of_msubst_pty_closed by eauto using ctxRst_closed_env.
  rewrite ctxdom_app_union in *.
  rewrite ctxRst_dom in * by eauto.
  my_set_solver.
Qed.

Lemma msubst_preserves_closed_pty_empty Γ Γv ρ :
  ctxRst Γ Γv ->
  closed_pty (ctxdom Γ) ρ ->
  closed_pty ∅ (m{Γv}p ρ).
Proof.
  intros. eapply msubst_preserves_closed_pty with (Γ':=[]); eauto.
  by simplify_list_eq.
Qed.

Lemma msubst_preserves_closed_hty Γ Γv Γ' τ :
  ctxRst Γ Γv ->
  closed_hty (ctxdom (Γ ++ Γ')) τ ->
  closed_hty (ctxdom Γ') (m{Γv}h τ).
Proof.
  intros HΓv H.
  sinvert H.
  econstructor. eauto using msubst_lc_hty, ctxRst_lc.
  rewrite fv_of_msubst_hty_closed by eauto using ctxRst_closed_env.
  rewrite ctxdom_app_union in *.
  rewrite ctxRst_dom in * by eauto.
  my_set_solver.
Qed.

Lemma msubst_preserves_closed_hty_empty Γ Γv τ:
  ctxRst Γ Γv ->
  closed_hty (ctxdom Γ) τ ->
  closed_hty ∅ (m{Γv}h τ).
Proof.
  intros. eapply msubst_preserves_closed_hty with (Γ':=[]); eauto.
  by simplify_list_eq.
Qed.

Lemma msubst_preserves_pty_measure ρ Γv:
  pty_measure ρ = pty_measure (m{Γv}p ρ).
Proof.
  msubst_tac. qauto using subst_preserves_pty_measure.
Qed.

Lemma msubst_preserves_hty_measure τ Γv:
  hty_measure τ = hty_measure (m{Γv}h τ).
Proof.
  msubst_tac. qauto using subst_preserves_hty_measure.
Qed.

Lemma msubst_preserves_basic_typing_tm Γ Γv :
  ctxRst Γ Γv ->
  forall Γ' e T,
    (⌊Γ⌋* ∪ Γ') ⊢t e ⋮t T ->
    Γ' ⊢t m{Γv}t e ⋮t T.
Proof.
  induction 1; intros; eauto.
  apply_eq H. cbn. apply map_empty_union.
  rewrite ctx_erase_app in H2.
  rewrite <- map_union_assoc in H2.
  apply IHctxRst in H2.
  rewrite msubst_insert;
    eauto using subst_commute_tm, ctxRst_closed_env,
                ptyR_closed_value, ctxRst_ok_insert.
  eapply basic_typing_subst_tm; cycle 1.
  eapply_eq H2.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_l. reflexivity.
  eapply basic_typing_weaken_value. apply map_empty_subseteq.
  apply ptyR_typed_closed in H1. simp_hyps.
  sinvert H1. apply_eq H6. eauto using pty_erase_msubst_eq.
Qed.

Lemma msubst_preserves_basic_typing_tm_empty Γ Γv :
  ctxRst Γ Γv ->
  forall e T,
    ( ⌊Γ⌋* ) ⊢t e ⋮t T ->
    ∅ ⊢t m{Γv}t e ⋮t T.
Proof.
  intros. eapply msubst_preserves_basic_typing_tm; eauto.
  rewrite map_union_empty. eauto.
Qed.

Lemma msubst_preserves_basic_typing_value Γ Γv :
  ctxRst Γ Γv ->
  forall Γ' v T,
    (⌊Γ⌋* ∪ Γ') ⊢t v ⋮v T ->
    Γ' ⊢t m{Γv}v v ⋮v T.
Proof.
  induction 1; intros; eauto.
  apply_eq H. cbn. apply map_empty_union.
  rewrite ctx_erase_app in H2.
  rewrite <- map_union_assoc in H2.
  apply IHctxRst in H2.
  rewrite msubst_insert;
    eauto using subst_commute_value, ctxRst_closed_env,
                ptyR_closed_value, ctxRst_ok_insert.
  eapply basic_typing_subst_value; cycle 1.
  eapply_eq H2.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_l. reflexivity.
  eapply basic_typing_weaken_value. apply map_empty_subseteq.
  apply ptyR_typed_closed in H1. simp_hyps.
  sinvert H1. apply_eq H6. eauto using pty_erase_msubst_eq.
Qed.

Lemma msubst_preserves_basic_typing_value_empty Γ Γv :
  ctxRst Γ Γv ->
  forall v T,
    ( ⌊Γ⌋* ) ⊢t v ⋮v T ->
    ∅ ⊢t m{Γv}v v ⋮v T.
Proof.
  intros. eapply msubst_preserves_basic_typing_value; eauto.
  rewrite map_union_empty. eauto.
Qed.

Lemma msubst_fvar_inv (Γv : env) v (x : atom) :
  closed_env Γv ->
  m{Γv}v v = x ->
  v = x /\ x ∉ dom Γv.
Proof.
  msubst_tac. my_set_solver.
  destruct r; simpl in H2; simplify_eq.
  case_decide; simplify_eq. exfalso.
  apply map_Forall_insert in H1; eauto. simp_hyps.
  unfold closed_value in *.
  cbn in *. qauto using non_empty_singleton.
  simp_hyps. split; eauto. subst.
  rewrite dom_insert. my_set_solver.
Qed.
