From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementType.
From CT Require Import Denotation.
From CT Require Import Instantiation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import Trace.
Import OperationalSemantics.
Import BasicTyping.
Import RefinementType.
Import Denotation.
Import Instantiation.
Import Qualifier.

(** Well-formedness *)
Definition wf_am (Γ: listctx pty) (A: am): Prop := closed_am (ctxdom ⦑ Γ ⦒) A.

Inductive wf_pty: listctx pty -> pty -> Prop :=
| wf_pty_base: forall Γ b ϕ,
    closed_pty (ctxdom ⦑ Γ ⦒) {: b | ϕ } -> wf_pty Γ {: b | ϕ }
| wf_pty_arr: forall Γ ρ T A B (L: aset),
    wf_pty Γ ρ ->
    amlist_typed B T ->
    (* NOTE: we do not allow empty union here; it does not affect
    expressiveness, as we can always use [aemp] instead. *)
    B <> [] ->
    (forall x, x ∉ L ->
          wf_am (Γ ++ [(x, ρ)]) (A ^a^ x) /\
          (forall Bi ρi, In (Bi, ρi) B ->
                    wf_am (Γ ++ [(x, ρ)]) (Bi ^a^ x)
          )
    ) ->
    (forall x, x ∉ L ->
          (forall Bi ρi, In (Bi, ρi) B ->
                    wf_pty (Γ ++ [(x, ρ)]) (ρi ^p^ x)
          )
    ) ->
    wf_pty Γ (-: ρ ⤑[: T | A ▶ B ]).

Inductive wf_hty: listctx pty -> hty -> Prop :=
| wf_hty_: forall Γ T A B,
    amlist_typed B T ->
    B <> [] ->
    wf_am Γ A ->
    (forall Bi ρi, In (Bi, ρi) B -> wf_am Γ Bi /\ wf_pty Γ ρi) ->
    wf_hty Γ [: T | A ▶ B ].

Notation " Γ '⊢WF' τ " := (wf_hty Γ τ) (at level 20, τ constr, Γ constr).
Notation " Γ '⊢WFp' τ " := (wf_pty Γ τ) (at level 20, τ constr, Γ constr).
Notation " Γ '⊢WFa' a " := (wf_am Γ a) (at level 20, a constr, Γ constr).

Definition subtyping (Γ: listctx pty) (τ1 τ2: hty) : Prop :=
  (* Assume [τ1] and [τ2] are valid [hty]s. *)
  ⌊ τ1 ⌋ = ⌊ τ2 ⌋ /\
  forall Γv, ctxRst Γ Γv -> forall e, ⟦(m{ Γv }h) τ1⟧ (m{ Γv }t e) → ⟦(m{ Γv }h) τ2⟧ (m{ Γv }t e).

Notation " Γ '⊢' τ1 '<⋮' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Reserved Notation "Γ '⊢' e '⋮t' τ" (at level 20).
Reserved Notation "Γ '⊢' e '⋮v' τ"  (at level 20).

(* The parameterized builtin typing relation (Δ). *)
Parameter builtin_typing_relation : listctx pty -> effop -> pty -> Prop.

(** Typing *)
Inductive term_type_check : listctx pty -> tm -> hty -> Prop :=
| TValue: forall Γ v ρ,
    Γ ⊢ v ⋮v ρ ->
    Γ ⊢ v ⋮t (pty_to_rty ρ)
| TSub: forall Γ e (τ1 τ2: hty),
    Γ ⊢WF τ2 ->
    Γ ⊢ e ⋮t τ1 ->
    Γ ⊢ τ1 <⋮ τ2 ->
    Γ ⊢ e ⋮t τ2
| TLetE: forall Γ e_x e Tx A T Bx_ρx BxB_ρ Bx_ρx_B_ρ (L: aset),
    Γ ⊢WF [: T | A ▶ BxB_ρ ] ->
    Γ ⊢ e_x ⋮t [: Tx | A ▶ Bx_ρx ] ->
    Forall2 (fun '(Bx, ρx) '(Bx', ρx', _, _) =>
               Bx = Bx' /\ ρx = ρx') Bx_ρx Bx_ρx_B_ρ ->
    Forall2 (fun '(BxB, ρ) '(Bx, _, B, ρ') =>
               BxB = aconcat Bx B /\ ρ = ρ') BxB_ρ Bx_ρx_B_ρ ->
    (forall x, x ∉ L ->
          forall Bxi ρxi Bi ρi,
            In (Bxi, ρxi, Bi, ρi) Bx_ρx_B_ρ ->
            (Γ ++ [(x, ρxi)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A Bxi ▶ [(Bi, ρi)]]) ->
    Γ ⊢ (tlete e_x e) ⋮t [: T | A ▶ BxB_ρ ]
| TApp: forall Γ (v1 v2: value) e ρ Tx A T Bx_ρx BxB_ρ Bx_ρx_B_ρ (L: aset),
    Γ ⊢WF [: T | A ^a^ v2 ▶ BxB_ρ ] ->
    Γ ⊢ v2 ⋮v ρ ->
    Γ ⊢ v1 ⋮v (-: ρ ⤑[: Tx | A ▶ Bx_ρx ]) ->
    Forall2 (fun '(Bx, ρx) '(Bx', ρx', _, _) =>
               Bx = Bx' /\ ρx = ρx') Bx_ρx Bx_ρx_B_ρ ->
    Forall2 (fun '(BxB, ρ) '(Bx, _, B, ρ') =>
               BxB = aconcat (Bx ^a^ v2) B /\ ρ = ρ') BxB_ρ Bx_ρx_B_ρ ->
    (forall x, x ∉ L ->
          forall Bxi ρxi Bi ρi,
            In (Bxi, ρxi, Bi, ρi) Bx_ρx_B_ρ ->
            (Γ ++ [(x, ρxi ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat (A ^a^ v2) (Bxi ^a^ v2) ▶ [(Bi, ρi)]]) ->
    Γ ⊢ (tletapp v1 v2 e) ⋮t [: T | A ^a^ v2 ▶ BxB_ρ ]
| TEffOp: forall Γ (op: effop) (v2: value) e ϕx A T Bx_ρx opϕB_ρ ϕ_B_ρ (L: aset),
    Γ ⊢WF [: T | A ^a^ v2 ▶ opϕB_ρ ] ->
    Γ ⊢ v2 ⋮v {:TNat | ϕx} ->
    Γ ⊢WFp (-: {:TNat | ϕx} ⤑[: ret_ty_of_op op | A ▶ Bx_ρx ]) ->
    builtin_typing_relation Γ op (-: {:TNat | ϕx} ⤑[: ret_ty_of_op op | A ▶ Bx_ρx ]) ->
    Forall2 (fun '(Bx, ρx) '(ϕ, _, _) =>
               Bx = aϵ /\ ρx = {: ret_ty_of_op op | ϕ}) Bx_ρx ϕ_B_ρ ->
    Forall2 (fun '(opϕB, ρ) '(ϕ, B, ρ') =>
               opϕB = aconcat (⟨ op | b1:v= v2 & ϕ ⟩) B /\ ρ = ρ') opϕB_ρ ϕ_B_ρ ->
    (forall x, x ∉ L ->
          forall ϕi Bi ρi,
            In (ϕi, Bi, ρi) ϕ_B_ρ ->
            (Γ ++ [(x, {: ret_ty_of_op op | ϕi} ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat (A ^a^ v2) (⟨ op | b1:v= v2 & b0:x= x ⟩) ▶ [(Bi, ρi)]]) ->
    Γ ⊢ (tleteffop op v2 e) ⋮t [: T | A ^a^ v2 ▶ opϕB_ρ ]
| TMatchb: forall Γ (v: value) e1 e2 ϕ τ (L : aset),
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v {:TBool | ϕ} ->
    (* We can also directly encode the path condition without mentioning [x]:
       {: TNat | (qual [# v] (fun V => V !!! 0 = (cbool true))%fin) & ϕ ^q^ v}
     *)
    (forall x, x ∉ L -> (Γ ++ [(x, {: TBool | b0:c=true & b0:v= v & ϕ})]) ⊢ e1 ⋮t τ) ->
    (forall x, x ∉ L -> (Γ ++ [(x, {: TBool | b0:c=false & b0:v= v & ϕ})]) ⊢ e2 ⋮t τ) ->
    Γ ⊢ (tmatchb v e1 e2) ⋮t τ
with value_type_check : listctx pty -> value -> pty -> Prop :=
| TConstant: forall Γ (c: constant),
    Γ ⊢WFp (mk_eq_constant c) ->
    Γ ⊢ c ⋮v (mk_eq_constant c)
| TVar: forall Γ (x: atom) ρ,
    Γ ⊢WFp ρ ->
    ctxfind Γ x = Some ρ ->
    Γ ⊢ x ⋮v ρ
| TLam: forall Γ Tx ρ e T A B (L: aset),
    Γ ⊢WFp (-: ρ ⤑[: T | A ▶ B ] ) ->
    (forall x, x ∉ L -> (Γ ++ [(x, ρ)]) ⊢ (e ^t^ x) ⋮t ([: T | A ▶ B ] ^h^ x)) ->
    Tx = ⌊ ρ ⌋ ->
    Γ ⊢ (vlam Tx e) ⋮v (-: ρ ⤑[: T | A ▶ B ])
| TLamFix: forall Γ (Tx : base_ty) ϕ e T A B (L: aset),
    Γ ⊢WFp (-: {: Tx | ϕ} ⤑[: T | A ▶ B ]) ->
    (* NOTE: should not open the whole type, because the first argument (bound
    variable 0) of the return type is not the fixed point function but [{: Tx |
    ϕ}]. The return type should be opened by [x]. *)
    (forall x, x ∉ L -> (Γ ++ [(x, {: Tx | ϕ})]) ⊢ (vlam (Tx ⤍ T) e) ^v^ x ⋮v (-: (-: {: Tx | b0:x≺ x & ϕ} ⤑[: T | A ▶ B ]) ⤑[: T | A ^a^ x ▶ B ^pa^ x])) ->
    Γ ⊢ (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e)) ⋮v (-: {: Tx | ϕ} ⤑[: T | A ▶ B ])
where
"Γ '⊢' e '⋮t' τ" := (term_type_check Γ e τ) and "Γ '⊢' e '⋮v' τ" := (value_type_check Γ e τ).


Scheme value_type_check_rec := Induction for value_type_check Sort Prop
    with term_type_check_rec := Induction for term_type_check Sort Prop.

Lemma pty_to_rty_wf Γ ρ :
  wf_pty Γ ρ ->
  wf_hty Γ (pty_to_rty ρ).
Proof.
  unfold pty_to_rty.
  induction 1.
  - cbn. econstructor.
    hnf. intros. qauto. eauto.
    repeat econstructor. my_set_solver.
    qsimpl. repeat econstructor. my_set_solver.
  - cbn. econstructor.
    hnf. intros. qauto. eauto.
    repeat econstructor. my_set_solver.
    qsimpl.
Qed.

Lemma subtyping_preserves_basic_typing Γ τ1 τ2 :
  Γ ⊢ τ1 <⋮ τ2 ->
  ⌊τ1⌋ = ⌊τ2⌋.
Proof.
  qauto.
Qed.

Lemma value_typing_regular_wf : forall (Γ: listctx pty) (v: value) (ρ: pty),
    Γ ⊢ v ⋮v ρ -> wf_pty Γ ρ
with tm_typing_regular_wf : forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ -> wf_hty Γ τ.
Proof.
  all: destruct 1; eauto using pty_to_rty_wf.
Qed.

(* Maybe move these lemmas to other files. *)
Lemma list_not_nil_ex {A} (xs : list A) :
  xs <> [] ->
  exists x, In x xs.
Proof.
  destruct xs; qauto.
Qed.

Lemma Forall2_In_l {A B} R (xs : list A) (ys : list B) :
  Forall2 R xs ys ->
  forall x, In x xs -> exists y, In y ys /\ R x y.
Proof.
  induction 1; qauto.
Qed.

Lemma Forall2_In_r {A B} R (xs : list A) (ys : list B) :
  Forall2 R xs ys ->
  forall y, In y ys -> exists x, In x xs /\ R x y.
Proof.
  induction 1; qauto.
Qed.

Ltac simpl_Forall2 :=
  repeat
    (match goal with
     | H : _ <> [] |- _ => apply list_not_nil_ex in H
     | H : Forall2 _ ?xs _, H' : In _ ?xs |- _ =>
         eapply Forall2_In_l in H; [ | apply H' ]
     | H : Forall2 _ _ ?ys, H' : In _ ?ys |- _ =>
         eapply Forall2_In_r in H; [ | apply H' ]
     end; simp_hyps; simplify_eq); set_fold_not.

Lemma union_list_subseteq_forall
  {A C} `{SemiSet A C}
  (Xs : list C) (Y : C):
  (forall X, In X Xs -> X ⊆ Y) ->
  ⋃ Xs ⊆ Y.
Proof.
  intros. induction Xs. my_set_solver.
  simpl.
  apply union_least.
  qauto.
  qauto.
Qed.

Lemma union_list_not_in
  {A C} `{SemiSet A C}
  (Xs : list C) x:
  (forall X, In X Xs -> x ∉ X) ->
  x ∉ ⋃ Xs.
Proof.
  intros. induction Xs. my_set_solver.
  simpl.
  apply not_elem_of_union. split; eauto.
  auto_apply. qauto.
  auto_apply. qauto.
Qed.

Lemma value_typing_regular_basic_typing: forall (Γ: listctx pty) (v: value) (ρ: pty),
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋
with tm_typing_regular_basic_typing: forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋.
Proof.
  all: destruct 1; cbn; subst;
    eauto using value_has_type, tm_has_type, ctx_erase_lookup.
  - econstructor.
    instantiate_atom_listctx.
    rewrite <- ctx_erase_app_r by my_set_solver.
    qauto.
  - econstructor.
    instantiate_atom_listctx.
    eapply value_typing_regular_basic_typing in H0.
    apply_eq H0. apply ctx_erase_app_r. my_set_solver.
  - erewrite <- subtyping_preserves_basic_typing; eauto.
  - econstructor. apply tm_typing_regular_basic_typing. eauto.
    instantiate_atom_listctx.
    sinvert H. simpl_Forall2.
    cbn. eapply_eq tm_typing_regular_basic_typing; eauto.
    rewrite ctx_erase_app_r by my_set_solver.
    f_equal. apply tm_typing_regular_wf in H0. sinvert H0. eauto.
  - econstructor; eauto.
    apply_eq value_typing_regular_basic_typing; eauto.
    instantiate_atom_listctx.
    sinvert H. simpl_Forall2.
    eapply_eq tm_typing_regular_basic_typing; eauto.
    rewrite ctx_erase_app_r by my_set_solver.
    rewrite <- pty_erase_open_eq.
    f_equal. apply value_typing_regular_wf in H1. sinvert H1. eauto.
  - econstructor; eauto.
    qauto.
    instantiate_atom_listctx.
    sinvert H. simpl_Forall2.
    apply_eq tm_typing_regular_basic_typing; eauto.
    rewrite ctx_erase_app_r by my_set_solver.
    f_equal.
  - auto_pose_fv x. repeat specialize_with x.
    econstructor. qauto.
    eapply basic_typing_strengthen_tm.
    rewrite <- ctx_erase_app_r.
    auto_apply. eauto.
    my_set_solver.
    my_set_solver.
    eapply basic_typing_strengthen_tm.
    rewrite <- ctx_erase_app_r.
    auto_apply. eauto.
    my_set_solver.
    my_set_solver.
Qed.

Lemma am_concat: forall A B α β,
    (a⟦A⟧) α -> (a⟦B⟧) β -> (a⟦ aconcat A B ⟧) (α ++ β).
Proof.
  intros.
  split.
  select! (a⟦_⟧ _) (fun H => apply langA_closed in H; sinvert H).
  repeat econstructor; eauto. my_set_solver.
  eauto.
Qed.

Lemma in_singleton {T1 T2: Type}: forall (a1 a1': T1) (a2 a2': T2), In (a1, a2) [(a1', a2')] -> a1 = a1' /\ a2 = a2'.
Proof.
  intros. inversion H. inversion H0; subst; auto. inversion H0.
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
  (* TODO: hintdb? *)
  eauto using subst_commute_value, subst_commute_tm, subst_commute_qualifier,
    subst_commute_pty, subst_commute_am, subst_commute_postam, subst_commute_hty.

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

Lemma msubst_bvar: forall Γv n, (m{Γv}v) (vbvar n) = vbvar n.
Proof.
  msubst_tac.
Qed.

Lemma msubst_constant: forall Γv (c: constant), (m{Γv}v) c = c.
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

Lemma msubst_arrty: forall Γv ρ T A B,
    closed_env Γv ->
    (m{Γv}p) (-:ρ⤑[:T|A▶B]) = (-:(m{Γv}p ρ)⤑[:T| (m{Γv}a A) ▶ (m{Γv}pa B) ]).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_bty: forall Γv b ϕ, closed_env Γv -> (m{Γv}p) {:b|ϕ} = {:b| (m{Γv}q) ϕ}.
Proof.
  msubst_tac. rewrite_msubst_insert.
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

Lemma msubst_hty: forall (Γv: env) T A B,
    closed_env Γv ->
    m{Γv}h [:T|A▶B] = [:T|m{Γv}a A ▶ m{Γv}pa B].
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma subst_postam: forall pa x v,
    {x := v}pa pa = map (fun '(B, ρ) => ({x := v}a B, {x := v}p ρ)) pa.
Proof.
  induction pa; simpl; intros; eauto.
  destruct a. simpl in *.
  f_equal. eauto.
Qed.

Lemma msubst_postam: forall (Γv: env) pa,
    closed_env Γv ->
    m{Γv}pa pa = map (fun '(B, ρ) => (m{Γv}a B, m{Γv}p ρ)) pa.
Proof.
  msubst_tac.
  - rewrite <- map_id at 1. apply map_ext.
    intros [].
    by rewrite !map_fold_empty.
  - rewrite subst_postam.
    rewrite map_map. apply map_ext.
    intros [].
    rewrite_msubst_insert.
Qed.

Lemma msubst_lete: forall (Γv: env) e_x e,
    closed_env Γv ->
    (m{Γv}t (tlete e_x e) = tlete ((m{Γv}t) e_x) ((m{Γv}t) e)).
Proof.
  msubst_tac. rewrite_msubst_insert.
Qed.

Lemma msubst_aϵ: forall (Γv: env),
    m{Γv}a aϵ = aϵ.
Proof.
  msubst_tac.
Qed.

Lemma msubst_concat: forall (Γv: env) A1 A2,
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

Lemma msubst_pty_to_rty: forall Γv ρ,
    closed_env Γv ->
    (m{Γv}h) (pty_to_rty ρ) = pty_to_rty (m{Γv}p ρ).
Proof.
  msubst_tac.
  unfold pty_to_rty.
  simpl. f_equal.
  - rewrite_msubst_insert.
    rewrite <- pty_erase_subst_eq. reflexivity.
  - rewrite_msubst_insert.
Qed.

Ltac msubst_simp :=
  match goal with
  | H: context [ m{ _ }h (pty_to_rty _) ] |- _ => rewrite msubst_pty_to_rty in H
  | |- context [ m{ _ }h (pty_to_rty _) ] => rewrite msubst_pty_to_rty
  | H: context [ m{ _ }h _ ] |- _ => rewrite msubst_hty in H
  | |- context [ m{ _ }h _ ] => rewrite msubst_hty
  | H: context [ m{ _ }p {: _ | _ } ] |- _ => rewrite msubst_bty in H
  | |- context [ m{ _ }p {: _ | _ } ] => rewrite msubst_bty
  | H: context [ m{ _ }p (-: _ ⤑[: _ | _ ▶ _ ]) ] |- _ => rewrite msubst_arrty in H
  | |- context [ m{ _ }p (-: _ ⤑[: _ | _ ▶ _ ]) ] => rewrite msubst_arrty
  | H: context [ m{ _ }a (aϵ) ] |- _ => rewrite msubst_aϵ in H
  | |- context [ m{ _ }a (aϵ) ] => rewrite msubst_aϵ
  | H: context [ m{ _ }a (aconcat _ _) ] |- _ => rewrite msubst_concat in H
  | |- context [ m{ _ }a (aconcat _ _) ] => rewrite msubst_concat
  | H: context [ m{ _ }a (aevent _ _) ] |- _ => rewrite msubst_aevent in H
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
  | H: context [ m{ _ }q (_ & _) ] |- _ => rewrite msubst_qualifier_and in H
  | |- context [ m{ _ }q (_ & _) ] => rewrite msubst_qualifier_and
  (* | H: context [ m{ _ }q _ ] |- _ => rewrite msubst_qualifier in H *)
  (* | |- context [ m{ _ }q _ ] => rewrite msubst_qualifier *)
  end; eauto using ctxRst_closed_env.

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

Lemma msubst_intro_postam: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~pa> v_x} ((m{Γv}pa) e) = (m{<[x:=v_x]> Γv}pa) ({k ~pa> x} e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
  msubst_tac.
  rewrite map_fold_empty.
  rewrite open_subst_same_postam. auto. my_set_solver.
  rewrite_msubst_insert.
  apply map_Forall_insert in H3; eauto.
  rewrite subst_commute_postam by my_set_solver.
  rewrite <- H0 by my_set_solver.
  by rewrite subst_open_postam_closed by qauto.
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
  rewrite fv_of_subst_pty by eauto. my_set_solver.
Qed.

Lemma msubst_hty_fv_subseteq Γv v_x τ:
  closed_env Γv ->
  closed_value v_x ->
  hty_fv (m{Γv}h τ) ⊆ hty_fv τ.
Proof.
  msubst_tac.
  rewrite fv_of_subst_hty by eauto. my_set_solver.
Qed.

Lemma msubst_postam_fv_subseteq Γv v_x pa:
  closed_env Γv ->
  closed_value v_x ->
  postam_fv (m{Γv}pa pa) ⊆ postam_fv pa.
Proof.
  msubst_tac.
  rewrite fv_of_subst_postam by eauto. my_set_solver.
Qed.

Lemma msubst_qualifier_fv_subseteq Γv v_x ϕ:
  closed_env Γv ->
  closed_value v_x ->
  qualifier_fv (m{Γv}q ϕ) ⊆ qualifier_fv ϕ.
Proof.
  msubst_tac.
  rewrite fv_of_subst_qualifier by eauto. my_set_solver.
Qed.

Lemma msubst_am_fv_subseteq Γv v_x a:
  closed_env Γv ->
  closed_value v_x ->
  am_fv (m{Γv}a a) ⊆ am_fv a.
Proof.
  msubst_tac.
  rewrite fv_of_subst_am by eauto. my_set_solver.
Qed.

Lemma msubst_tm_fv_subseteq Γv v_x t:
  closed_env Γv ->
  closed_value v_x ->
  fv_tm (m{Γv}t t) ⊆ fv_tm t.
Proof.
  msubst_tac.
  rewrite fv_of_subst_tm by eauto. my_set_solver.
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

Lemma msubst_insert_fresh_postam Γv x v_x pa:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ postam_fv pa ->
  (m{<[x:=v_x]> Γv}pa) pa = (m{Γv}pa) pa.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_postam.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_postam_fv_subseteq by eauto. my_set_solver.
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

Lemma lc_msubst_pty Γv (ρ: pty):
  lc_pty (m{Γv}p ρ) ->
  map_Forall (fun _ v => lc (treturn v)) Γv ->
  lc_pty ρ.
Proof.
  msubst_tac.
  apply map_Forall_insert in H2; eauto. simp_hyps.
  eauto using lc_subst_pty.
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

Lemma ctxRst_ctxfind Γ Γv x ρ :
  ctxRst Γ Γv ->
  ctxfind Γ x = Some ρ ->
  exists (v : value), Γv !! x = Some v /\ p⟦ m{ Γv }p ρ ⟧ v.
Proof.
  induction 1.
  - easy.
  - intros.
    select (ctxfind (_ ++ _) _ = _)
      (fun H => apply ctxfind_app in H; eauto using ok_ctx_ok).

    assert (forall (v' : value), (p⟦(m{env}p) ρ⟧) v' ->
                            (p⟦(m{<[x0:=v]> env}p) ρ⟧) v'). {
      select (p⟦ _ ⟧ _) (fun H => apply ptyR_typed_closed in H). simp_hyps.
      intros.
      apply ptyR_msubst_insert_eq; eauto using ctxRst_closed_env.
      select (_ ⊢t _ ⋮t _)
        (fun H => apply basic_typing_contains_fv_tm in H; simpl in H).
      my_set_solver.
      select (ok_ctx _) (fun H => apply ok_ctx_ok in H; apply ok_post_destruct in H).
      srewrite ctxRst_dom.
      simp_hyps.
      apply not_elem_of_dom. eauto.
    }

    destruct_or!; simp_hyps.
    + eexists. split; eauto.
      assert (x <> x0). {
        select (ok_ctx _) (fun H => sinvert H); listctx_set_simpl.
        select (ctxfind _ _ = _) (fun H => apply ctxfind_some_implies_in_dom in H).
        my_set_solver.
      }
      by simplify_map_eq.
    + simpl in *.
      case_decide; try easy. simplify_eq.
      eexists. split; eauto. by simplify_map_eq.
Qed.

Lemma ctxRst_ok_insert Γ Γv x ρ :
  ctxRst Γ Γv ->
  ok_ctx (Γ ++ [(x, ρ)]) ->
  Γv !! x = None.
Proof.
  inversion 2; listctx_set_simpl.
  rewrite ctxRst_dom in * by eauto.
  by apply not_elem_of_dom.
Qed.

Lemma postam_msubst_in: forall (Γv: env) (A: am) (ρ: pty) (B: postam),
    closed_env Γv ->
    In (A, ρ) (m{Γv}pa B) ->
    exists A' ρ', A = m{Γv}a A' /\ ρ = m{Γv}p ρ' /\ In (A', ρ') B.
Proof.
  intros *. revert A ρ. apply_msubst_ind; intros; eauto.
  apply postam_subst_in in H2. simp_hyps. subst.
  gen_closed_env.
  apply H0 in H2; eauto. simp_hyps. subst.
  repeat esplit; eauto; rewrite_msubst_insert.
Qed.

Lemma postam_in_msubst: forall (Γv: env) (A: am) (ρ: pty) (B: postam),
    closed_env Γv ->
    In (A, ρ) B ->
    In ((m{Γv}a) A, (m{Γv}p) ρ) ((m{Γv}pa) B).
Proof.
  intros *. revert A ρ. apply_msubst_ind; intros; eauto.
  gen_closed_env.
  eapply postam_in_subst in H0; eauto.
  rewrite_msubst_insert.
Qed.

(* move some of these lemmas to another file? *)
Lemma amlist_typed_open B k v_x T:
  amlist_typed B T ->
  amlist_typed ({k ~pa> v_x} B) T.
Proof.
  intros. hnf in *.
  intros.
  apply postam_open_in in H0. simp_hyps. subst.
  rewrite <- pty_erase_open_eq.
  eauto.
Qed.

Lemma subst_amlist_typed: forall B T x v,
    amlist_typed B T ->
    amlist_typed ({x := v}pa B) T.
Proof.
  intros; hnf in *; intros.
  apply postam_subst_in in H0. simp_hyps. subst.
  rewrite <- pty_erase_subst_eq.
  eauto.
Qed.


Lemma msubst_amlist_typed: forall (Γv: env) B T,
    amlist_typed B T ->
    amlist_typed ((m{Γv}pa) B) T.
Proof.
  msubst_tac.
  eauto using subst_amlist_typed.
Qed.

Lemma subst_preserves_valid_pty x (v : value) ρ:
  lc v ->
  valid_pty ρ ->
  valid_pty ({x:=v}p ρ).
Proof.
  intros Hlc.
  induction 1; simpl; econstructor; eauto using subst_amlist_typed.
  instantiate_atom_listctx.
  apply in_map_iff in H4. simp_hyps. simpl in *.
  eapply_eq H2. eauto.
  apply subst_open_var_pty; eauto. my_set_solver.
Qed.

Lemma subst_preserves_valid_hty x (v : value) τ:
  lc v ->
  valid_hty τ ->
  valid_hty ({x:=v}h τ).
Proof.
  intros Hlc.
  induction 1; simpl; econstructor; eauto using subst_amlist_typed.
  intros.
  apply postam_subst_in in H1. simp_hyps. subst.
  eauto using subst_preserves_valid_pty.
Qed.

Lemma subst_preserves_closed_pty Γ x (v : value) ρ' ρ:
  lc v ->
  fv_value v ⊆ ctxdom ⦑Γ⦒ ->
  closed_pty (ctxdom ⦑Γ ++ [(x, ρ')]⦒) ρ ->
  closed_pty (ctxdom ⦑Γ⦒) ({x:=v}p ρ).
Proof.
  intros Hlc Hc H.
  sinvert H.
  econstructor. eauto using subst_preserves_valid_pty.
  eauto using subst_lc_pty.
  rewrite remove_arr_pty_ctx_dom_union in *.
  rewrite union_mono_l in * by apply remove_arr_pty_ctx_dom_singleton.
  rewrite fv_of_subst_pty. my_set_solver.
Qed.

Lemma subst_preserves_closed_hty Γ x (v : value) ρ' τ:
  lc v ->
  closed_value v ->
  closed_hty (ctxdom ⦑Γ ++ [(x, ρ')]⦒) τ ->
  closed_hty (ctxdom ⦑Γ⦒) ({x:=v}h τ).
Proof.
  intros Hlc Hc H. sinvert H.
  econstructor. eauto using subst_preserves_valid_hty.
  eauto using subst_lc_hty.
  rewrite remove_arr_pty_ctx_dom_union in *.
  rewrite union_mono_l in * by apply remove_arr_pty_ctx_dom_singleton.
  rewrite fv_of_subst_hty_closed by eauto.
  my_set_solver.
Qed.

Lemma msubst_preserves_closed_pty Γ Γv :
  ctxRst Γ Γv ->
  forall Γ' ρ,
    closed_pty (ctxdom ⦑Γ ++ Γ'⦒) ρ ->
    closed_pty (ctxdom ⦑Γ'⦒) (m{Γv}p ρ).
Proof.
  induction 1; simpl; intros; eauto.
  simplify_list_eq.
  apply IHctxRst in H2.
  rewrite msubst_insert;
    eauto using subst_commute_pty, ctxRst_closed_env,
                ptyR_closed_value, ctxRst_ok_insert.
  rewrite <- app_one_is_cons in *.
  rewrite remove_arr_pty_ctx_dom_app_commute in *.
  eapply subst_preserves_closed_pty; eauto using ptyR_lc.
  apply ptyR_closed_value in H1. my_set_solver.
Qed.

Lemma msubst_preserves_closed_pty_empty Γ Γv :
  ctxRst Γ Γv ->
  forall ρ,
    closed_pty (ctxdom ⦑Γ⦒) ρ ->
    closed_pty ∅ (m{Γv}p ρ).
Proof.
  intros.
  eapply msubst_preserves_closed_pty with (Γ' := []); eauto.
  simplify_list_eq. eauto.
Qed.

Lemma msubst_preserves_closed_hty Γ Γv :
  ctxRst Γ Γv ->
  forall Γ' τ,
    closed_hty (ctxdom ⦑Γ ++ Γ'⦒) τ ->
    closed_hty (ctxdom ⦑Γ'⦒) (m{Γv}h τ).
Proof.
  induction 1; simpl; intros; eauto.
  simplify_list_eq.
  apply IHctxRst in H2.
  rewrite msubst_insert;
    eauto using subst_commute_hty, ctxRst_closed_env,
                ptyR_closed_value, ctxRst_ok_insert.
  rewrite <- app_one_is_cons in *.
  rewrite remove_arr_pty_ctx_dom_app_commute in *.
  eapply subst_preserves_closed_hty; eauto using ptyR_closed_value, ptyR_lc.
Qed.

Lemma msubst_preserves_closed_hty_empty Γ Γv :
  ctxRst Γ Γv ->
  forall τ,
    closed_hty (ctxdom ⦑Γ⦒) τ ->
    closed_hty ∅ (m{Γv}h τ).
Proof.
  intros.
  eapply msubst_preserves_closed_hty with (Γ' := []); eauto.
  simplify_list_eq. eauto.
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
  sinvert H3. apply_eq H6. eauto using pty_erase_msubst_eq.
Qed.

Lemma msubst_preserves_basic_typing_tm_empty Γ Γv :
  ctxRst Γ Γv ->
  forall e T,
    (⌊Γ⌋*) ⊢t e ⋮t T ->
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
  sinvert H3. apply_eq H6. eauto using pty_erase_msubst_eq.
Qed.

Lemma msubst_preserves_basic_typing_value_empty Γ Γv :
  ctxRst Γ Γv ->
  forall v T,
    (⌊Γ⌋*) ⊢t v ⋮v T ->
    ∅ ⊢t m{Γv}v v ⋮v T.
Proof.
  intros. eapply msubst_preserves_basic_typing_value; eauto.
  rewrite map_union_empty. eauto.
Qed.

Lemma wf_pty_closed Γ ρ :
  wf_pty Γ ρ ->
  closed_pty (ctxdom ⦑ Γ ⦒) ρ.
Proof.
  induction 1; eauto.
  sinvert IHwf_pty.
  econstructor.
  - econstructor; eauto.
    instantiate_atom_listctx.
    eapply H4; eauto.
  - econstructor; eauto.
    instantiate_atom_listctx.
    apply H2.
    intros. repeat specialize_with x.
    eapply H2; eauto.
    intros. repeat specialize_with x.
    eapply H4; eauto.
  - simpl.
    repeat apply union_least. eauto. {
      auto_pose_fv x. repeat specialize_with x. simp_hyps.
      sinvert H2.
      rewrite <- open_fv_am' in *.
      rewrite remove_arr_pty_ctx_dom_union in *.
      rewrite union_mono_l in * by apply remove_arr_pty_ctx_dom_singleton.
      my_set_solver.
    }
    apply union_list_subseteq_forall.
    setoid_rewrite in_map_iff.
    intros. simp_hyps. set_fold_not. simpl in *. subst.
    auto_pose_fv x. repeat specialize_with x. simp_hyps.
    sinvert H2. sinvert H4.
    rewrite <- open_fv_am' in *.
    rewrite <- open_fv_pty' in *.
    rewrite remove_arr_pty_ctx_dom_union in *.
    rewrite union_mono_l in * by apply remove_arr_pty_ctx_dom_singleton.
    my_set_solver.
Qed.

Lemma wf_hty_closed Γ τ :
  wf_hty Γ τ ->
  closed_hty (ctxdom ⦑ Γ ⦒) τ.
Proof.
  intros H. sinvert H. simp_hyps. sinvert H2.
  econstructor.
  econstructor; eauto.
  intros; eapply wf_pty_closed in H; eauto. sinvert H. eauto.
  econstructor; eauto.
  intros; sinvert H3.
  intros; eapply wf_pty_closed in H; eauto. sinvert H. eauto.
  simpl.
  apply union_least. eauto.
  apply union_list_subseteq_forall.
  intros. rewrite in_map_iff in *. simp_hyps. subst. simpl in *.
  sinvert H3.
  eapply wf_pty_closed in H; eauto. sinvert H.
  my_set_solver.
Qed.

Lemma wf_pty_arr_not_in Γ ρ T' A' B' T A B :
  Γ ⊢WFp (-:-:ρ⤑[:T'|A'▶B']⤑[:T|A▶B]) ->
  exists (L : aset), forall (x : atom), x ∉ L -> x # [:T|A▶B] ^h^ x.
Proof.
  intros H. sinvert H.
  eexists. instantiate_atom_listctx.
  apply not_elem_of_union. split.
  - sinvert H0.
    rewrite remove_arr_pty_ctx_dom_union in *.
    simpl in *.
    rewrite union_empty_r_L in *.
    rewrite remove_arr_pty_ctx_dom_subseteq in *.
    my_set_solver.
  - apply union_list_not_in.
    intros.
    rewrite in_map_iff in *. simp_hyps.
    apply postam_open_in in H5. simp_hyps. subst. simpl in *.
    sinvert H1; eauto.
    eapply wf_pty_closed in H9; eauto. sinvert H9.
    rewrite remove_arr_pty_ctx_dom_union in *.
    simpl in *.
    rewrite union_empty_r_L in *.
    rewrite remove_arr_pty_ctx_dom_subseteq in *.
    my_set_solver.
Qed.

Lemma value_reduction_refl: forall α β (v1: value) v2, α ⊧ v1 ↪*{ β} v2 -> v2 = v1 /\ β = [].
Proof.
  intros * H.
  sinvert H; easy.
Qed.

Ltac reduction_simp :=
  match goal with
  | H: _ ⊧ (treturn _) ↪*{ _ } _  |- _ =>
      apply value_reduction_refl in H; simp_hyps; simplify_eq
  end.

Lemma reduction_tlete:  forall e_x e α β (v : value),
    α ⊧ tlete e_x e ↪*{ β } v ->
    (exists (βx βe: trace) (v_x: value),
      β = βx ++ βe /\ α ⊧ e_x ↪*{ βx } v_x /\ (α ++ βx) ⊧ (e ^t^ v_x) ↪*{ βe } v).
Proof.
  intros.
  remember (tlete e_x e). remember (treturn v).
  revert dependent e_x.
  induction H; intros; subst. easy.
  sinvert H.
  - efeed specialize IHmultistep; eauto.
    simp_hyps.
    eexists _, _, _. split; [ | split ]; cycle 1.
    econstructor; eauto. simplify_list_eq. eauto.
    simplify_list_eq. eauto.
  - repeat esplit. econstructor; eauto. eauto.
Qed.

Lemma reduction_tlete':  forall e_x e α βx βe (v_x v : value),
    (* NOTE: This condition is unnecessary as it should be implied by the
    regularity lemma. Remove later when we bother proving a few more naming
    lemmas. *)
    body e ->
    α ⊧ e_x ↪*{ βx } v_x ->
    (α ++ βx) ⊧ (e ^t^ v_x) ↪*{ βe } v ->
    α ⊧ tlete e_x e ↪*{ βx ++ βe } v.
Proof.
  intros * Hb H. remember (treturn v_x).
  induction H; intros; subst.
  - econstructor; eauto using STLetE2.
  - simp_hyps.
    simplify_list_eq.
    econstructor.
    econstructor; eauto.
    eauto.
Qed.

Lemma reduction_mk_app_e_v α β (f v_x v : value) :
  lc v_x ->
  α ⊧ mk_app_e_v f v_x ↪*{ β} v ->
  α ⊧ tletapp f v_x (vbvar 0) ↪*{ β} v.
Proof.
  intros Hlc H.
  sinvert H. sinvert H0. easy.
  simpl in *. simplify_list_eq.
  rewrite open_rec_lc_value in * by eauto. eauto.
Qed.

Lemma reduction_mk_app_e_v' α β (f v_x v : value) :
  α ⊧ tletapp f v_x (vbvar 0) ↪*{ β} v ->
  α ⊧ mk_app_e_v f v_x ↪*{ β} v.
Proof.
  intros H.
  assert (lc v_x). {
    apply multi_step_regular1 in H. sinvert H. eauto.
  }
  eapply_eq multistep_step.
  eapply STLetE2.
  apply multi_step_regular1 in H. sinvert H. eauto.
  (* Probably should be a lemma. *)
  eexists. instantiate_atom_listctx.
  simpl. apply letapp_lc_body. repeat split; eauto using lc.
  by rewrite open_rec_lc_value.
  simpl. simplify_list_eq. rewrite open_rec_lc_value; eauto.
  eauto.
Qed.

Lemma reduction_letapplam α Tb e (v_x : value) β (v : value) :
  lc v_x ->
  α ⊧ mk_app_e_v (vlam Tb e) v_x ↪*{ β} v ->
  α ⊧ e ^t^ v_x ↪*{ β} v.
Proof.
  intros Hlc H.
  sinvert H.
  sinvert H0; try easy.
  simpl in H1.
  rewrite open_rec_lc_value in H1 by auto.
  sinvert H1. sinvert H.
  apply reduction_tlete in H0.
  simp_hyps. simpl in *.
  sinvert H2; try easy.
  simplify_list_eq; eauto.
Qed.

Lemma reduction_letapplam' α Tb e (v_x : value) β (v : value) :
  lc v_x ->
  (* NOTE: This condition is unnecessary as it should be implied by the
  regularity lemma. *)
  body e ->
  α ⊧ e ^t^ v_x ↪*{ β} v ->
  α ⊧ mk_app_e_v (vlam Tb e) v_x ↪*{ β} v.
Proof.
  intros Hlc Hb H.
  eapply_eq multistep_step.
  eapply STLetE2.
  qauto using lc_abs_iff_body.
  (* probably should be a lemma. *)
  eexists. instantiate_atom_listctx.
  simpl. apply letapp_lc_body. repeat split; eauto using lc.
  by rewrite open_rec_lc_value.
  simpl. econstructor.
  econstructor. eauto. eauto.
  by rewrite open_rec_lc_value.
  rewrite open_rec_lc_value by eauto.
  simplify_list_eq. eapply reduction_tlete'; eauto.
  simpl. econstructor. eauto using multi_step_regular2.
  simplify_list_eq. auto.
Qed.

Lemma reduction_tletapp:  forall v1 v2 e α β (v : value),
    α ⊧ tletapp v1 v2 e ↪*{ β} v ->
    (exists (βx βe: trace) (v_x: value),
      β = βx ++ βe /\ α ⊧ mk_app_e_v v1 v2 ↪*{ βx } v_x /\
        (α ++ βx) ⊧ (e ^t^ v_x) ↪*{ βe } v).
Proof.
  intros.
  remember (tletapp v1 v2 e). remember (treturn v).
  revert dependent v2.
  revert dependent v1.
  induction H; intros; subst. easy.
  simp_hyps. sinvert H.
  - eapply reduction_tlete in H0. simp_hyps.
    simplify_list_eq.
    eexists _, _, _. split; [| split]; eauto using reduction_letapplam'.
  - simplify_list_eq.
    efeed specialize H1; eauto. simp_hyps.
    eexists _, _, _.
    repeat split; cycle 1.

    (* Maybe this should be a lemma about [vfix]. *)
    apply reduction_mk_app_e_v in H.
    apply reduction_mk_app_e_v'.
    econstructor. econstructor; eauto.
    simplify_list_eq. eauto.
    apply multi_step_regular1 in H0.
    sinvert H0. eauto.

    simplify_list_eq. eauto.
    simplify_list_eq. eauto.
Qed.

Lemma reduction_tleteffop:  forall op v2 e α β (v : value),
    α ⊧ (tleteffop op v2 e) ↪*{ β} v ->
    exists (c2 c_x: constant) β',
      v2 = c2 /\ β = ev{ op ~ c2 := c_x } :: β' /\
        α ⊧{op ~ c2}⇓{ c_x } /\ (α ++ [ev{op ~ c2 := c_x}]) ⊧ (e ^t^ c_x) ↪*{ β'} v .
Proof.
  intros.
  sinvert H. sinvert H0.
  eauto 10.
Qed.

Lemma reduction_matchb_true:  forall e1 e2 α β (v : value),
    α ⊧ tmatchb true e1 e2 ↪*{ β} v -> α ⊧ e1 ↪*{ β} v.
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.

Lemma reduction_matchb_false:  forall e1 e2 α β (v : value),
    α ⊧ tmatchb false e1 e2 ↪*{ β} v -> α ⊧ e2 ↪*{ β} v.
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.

Lemma denotation_application_base_arg:
  forall (b: base_ty) ϕ T A B (Tb: ty) e,
    Tb = b ->
    ∅ ⊢t vlam Tb e ⋮t Tb ⤍ T ->
    closed_pty ∅ (-:{:b|ϕ}⤑[:T|A▶B]) ->
    (forall(v: value), p⟦ {:b|ϕ} ⟧ v -> ⟦ [:T | A ^a^ v ▶ B ^pa^ v ] ⟧ (e ^t^ v)) ->
    p⟦ -: {:b|ϕ} ⤑[:T|A▶B] ⟧ (vlam Tb e).
Proof.
  intros.
  subst.
  repeat (split; eauto).
  intros.
  dup_hyp H3 (fun H => apply H2 in H).
  hnf in H6.
  cbn in H6.
  simp_hyps.
  efeed specialize H9; eauto using amlist_typed_open.
  eapply reduction_letapplam; eauto.
  simp_hyps.
  apply postam_open_in in H7. simp_hyps. subst.
  repeat esplit; eauto.
  apply_eq H11.
  rewrite <- pty_erase_open_eq. eauto.
Qed.

Lemma denotation_application_arr_arg:
  forall ρx (Tx: ty) Ax Bx T A B Te e,
    Te = (⌊ ρx ⌋ ⤍ Tx) ->
    ∅ ⊢t vlam Te e ⋮t Te ⤍ T ->
    closed_pty ∅ (-: -: ρx ⤑[:Tx|Ax▶Bx] ⤑[:T|A▶B]) ->
    (forall (v: value), p⟦ -: ρx ⤑[:Tx|Ax▶Bx] ⟧ v -> ⟦ [:T | A ▶ B ] ⟧ (e ^t^ v)) ->
    p⟦ -: -: ρx ⤑[:Tx|Ax▶Bx] ⤑[:T|A▶B] ⟧ (vlam Te e).
Proof.
  intros.
  subst.
  repeat (split; eauto).
  intros.
  dup_hyp H3 (fun H => apply H2 in H).
  hnf in H6.
  cbn in H6.
  simp_hyps.
  efeed specialize H7; eauto using amlist_typed_open.
  eapply reduction_letapplam; eauto using ptyR_lc.
  simp_hyps.
  repeat esplit; eauto.
  apply_eq H11.
  eauto.
Qed.

Lemma denotation_application_fixed:
  forall (b: base_ty) ϕ T A B e,
    ∅ ⊢t vfix (b ⤍ T) (vlam (b ⤍ T) e) ⋮t b ⤍ T ->
    closed_pty ∅ (-:{:b|ϕ}⤑[:T|A▶B]) ->
    (forall(v: value),
        p⟦ {:b|ϕ} ⟧ v ->
        p⟦ (-:-:({:b|(b0:v≺ v) & ϕ})⤑[:T|A▶B]⤑[:T|A ^a^ v▶B ^pa^ v]) ⟧
          ((vlam (b ⤍ T) e) ^t^ v)) ->
    p⟦ -: {:b|ϕ} ⤑[:T|A▶B] ⟧ (vfix (b ⤍ T) (vlam (b ⤍ T) e)).
Proof.
  intros * Ht Hc H.
  repeat (split; eauto).
  intros Hamlist v_x.
  induction v_x using (well_founded_induction constant_lt_well_founded).
  rename H0 into IH.
  intros.
  specialize (H _ H0).
  destruct H as (Heq & Hta & Hca & H).
  move H at bottom.
  simpl pty_open in H.
  cbn iota in H.
  change (map _ B) with (pam_open 1 v_x B) in *.
  change (pty_erase_ ?e) with (erase e) in *.
  feed specialize H. {
    eauto using amlist_typed_open.
  }
  specialize (H (vfix (b ⤍ T) (vlam (b ⤍ T) e))).
  feed specialize H. {
    split. eauto. split. eauto. split.
    (* Should be a congruence lemma. *)
    clear - Hca.
    sinvert Hca.
    econstructor. sinvert H. eauto.
    sinvert H0. eauto. my_set_solver.

    intros.
    assert (v_x0 ≺ v_x /\ (p⟦{:b|ϕ}⟧) v_x0). {
      clear - H0 H4.
      apply ptyR_typed_closed in H0. destruct H0 as (_&_&H0).
      cbn in H4. simp_hyps.
      sinvert H1.
      dup_hyp H6 (fun H => apply empty_basic_typing_base_const_exists in H).
      simp_hyps. specialize (H2 c [] []). feed specialize H2.
      econstructor. econstructor.
      unfold bpropR in H2.
      rewrite !qualifier_and_open in H2.
      rewrite denote_qualifier_and in H2.
      simpl in H2. simp_hyps.
      split; eauto.
      split. eauto. split. econstructor. eauto.
      split. eauto.
      intros. apply value_reduction_refl in H3.
      simp_hyps. unfold bpropR. eauto.
    }
    simp_hyps.
    eauto.
  }
  (* lemma *)
  apply reduction_mk_app_e_v in H2.
  sinvert H2. 2: eauto using ptyR_closed_value.
  sinvert H3. simplify_list_eq.
  apply reduction_mk_app_e_v' in H4.
  specialize (H _ _ _ H1 H4).
  clear IH H0.
  simp_hyps.
  apply postam_open_in in H.
  simp_hyps. subst. eauto.
Qed.

Lemma pty_to_rty_preserves_closed: forall (ρ: pty) d,
    closed_pty d ρ -> closed_hty d (pty_to_rty ρ).
Proof.
  inversion 1.
  repeat econstructor; try solve [hnf; qauto]. qsimpl.
  cbn. repeat my_set_solver.
Qed.

Lemma denotation_value_pure: forall (ρ: pty) (v: value), p⟦ ρ ⟧ v <-> ⟦pty_to_rty ρ ⟧ v.
Proof.
  split; simpl; intros.
  - dup_hyp H (fun H => apply ptyR_typed_closed in H).
    simp_hyps.
    split; simpl; eauto. split; eauto using pty_to_rty_preserves_closed.
    intros Hamlist α β v' Hα Hstepv. reduction_simp.
    exists aϵ, ρ. split. unfold In. left; auto. split; auto. repeat constructor; auto.
  - destruct H as (Ht & Hclose & H).
    cbn in *.
    assert (amlist_typed [(aϵ, ρ)] ⌊ρ⌋) as Hamlist. {
      clear. hnf. qauto.
    }
    specialize (H Hamlist [] [] v).
    assert (closed_am ∅ (astar ∘) ∧ repeat_tr (a⟦∘⟧) []) as H1. {
      split; auto. repeat constructor; simpl; auto. econstructor.
    }
    assert ([] ⊧ v ↪*{ [] } v) as Hstepv. {
      econstructor.
      eauto using basic_typing_regular_tm.
    }
    specialize (H H1 Hstepv). mydestr. apply in_singleton in H. mydestr; subst; auto.
Qed.

Lemma closed_bool_typed_value: forall v, ∅ ⊢t v ⋮v TBool -> v = true \/ v = false.
Proof.
  intros. inversion H.
  - destruct c. destruct b; subst; auto. inversion H3.
  - subst. inversion H0.
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

Lemma msubst_constant_remove_arr_pty_ctx Γ Γv v (c : constant):
  ctxRst Γ Γv ->
  m{Γv}v v = c ->
  fv_value v ⊆ ctxdom ⦑ Γ ⦒.
Proof.
  induction 1; simpl.
  - unfold msubst. rewrite map_fold_empty.
    my_set_solver.
  - rewrite_msubst_insert; eauto using ctxRst_closed_env, ptyR_closed_value.
    2 : {
      sinvert H0; listctx_set_simpl.
      apply not_elem_of_dom.
      by srewrite ctxRst_dom.
    }
    intros Hv.
    sdestruct (m{env}v v); simpl in Hv; simplify_eq.
    simp_hyps. rewrite remove_arr_pty_ctx_dom_union. my_set_solver.
    case_decide; simplify_eq.
    apply msubst_fvar_inv in Heqv1; eauto using ctxRst_closed_env.
    simp_hyps. subst. simpl.
    rewrite remove_arr_pty_ctx_dom_union.
    destruct ρ; simpl. my_set_solver.
    exfalso. apply ptyR_typed_closed in H1.
    simp_hyps.
    rewrite <- pty_erase_msubst_eq in *. simpl in *.
    sinvert H2. sinvert H6.
Qed.

Lemma closed_hty_congr d T A B :
  closed_am d A ->
  (forall Bi ρi, In (Bi, ρi) B -> closed_am d Bi /\ closed_pty d ρi) ->
  amlist_typed B T ->
  closed_hty d [:T|A▶B].
Proof.
  intros. sinvert H.
  simp_hyps.
  econstructor.
  - econstructor; eauto.
    intros. sinvert H.
  - econstructor; eauto.
    intros. sinvert H0.
    intros. sinvert H.
  - simpl. apply union_least; eauto.
    apply union_list_subseteq_forall.
    intros. srewrite in_map_iff. simp_hyps. simpl in *. subst.
    sinvert H. sinvert H0. my_set_solver.
Qed.

Definition builtinR op ρx A B :=
  forall (v_x: constant),
    p⟦ ρx ⟧ v_x ->
    forall α, a⟦ A ^a^ v_x ⟧ α ->
         (forall (c: constant),
             α ⊧{op ~ v_x}⇓{ c } ->
             exists (Bi : am) ρi, In (Bi, ρi) B /\
                     p⟦ ρi ^p^ v_x ⟧ c).

Definition well_formed_builtin_typing := forall Γ op ρx A B,
    builtin_typing_relation Γ op (-: ρx ⤑[: ret_ty_of_op op | A ▶ B ]) ->
    forall Γv,
      ctxRst Γ Γv ->
      builtinR op (m{Γv}p ρx) (m{Γv}a A) (m{Γv}pa B).

Ltac simpl_fv :=
  do_hyps (fun H => try match type of H with
                    | _ ∉ _ =>
                        simpl in H; rewrite ?ctxRst_dom in H by eassumption
                    end).

(* At some point the proof is very slow without marking [msubst] opaque. *)
Opaque msubst.

Theorem fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ ->
    forall Γv, ctxRst Γ Γv -> ⟦ msubst hty_subst Γv τ ⟧ (msubst tm_subst Γv e).
Proof.
  intros HWFbuiltin.
  apply (term_type_check_rec
           (fun Γ (v: value) ρ _ =>
              forall Γv, ctxRst Γ Γv -> p⟦ m{Γv}p ρ ⟧ (m{Γv}v v))
           (fun Γ e (τ: hty) _ =>
              forall Γv, ctxRst Γ Γv -> ⟦ m{Γv}h τ ⟧ (m{Γv}t e))
        ).
  (* [TConstant] *)
  - intros Γ c HWF Γv HΓv. repeat msubst_simp.
    assert ((m{Γv}p) (mk_eq_constant c) = (mk_eq_constant c)) as Htmp. {
      unfold mk_eq_constant, mk_q_bvar_eq_val.
      repeat (simpl; msubst_simp).
      rewrite msubst_qualifier; eauto using ctxRst_closed_env.
      repeat (simpl; msubst_simp).
    }
    rewrite Htmp; clear Htmp.
    simpl.
    split. eauto. split. repeat econstructor.
    split. unshelve (repeat econstructor). exact ∅. simpl. repeat my_set_solver.
    intros. unfold bpropR. simpl.
    apply value_reduction_refl in H.
    simp_hyps. eauto.

  (* [TVar] *)
  - intros Γ x ρ Hwf Hfind Γv HΓv. repeat msubst_simp.
    eapply ctxRst_ctxfind in HΓv; eauto.
    qauto.

  (* [TLam] *)
  - intros Γ Tx ρ e T A B L HWF Ht HDe He Γv HΓv. repeat msubst_simp.
    assert (∅ ⊢t vlam Tx ((m{Γv}t) e) ⋮t Tx ⤍ T) as Hlam. {
      econstructor. econstructor.
      instantiate_atom_listctx.
      rewrite <- msubst_open_var_tm by
        (eauto using ctxRst_closed_env, ctxRst_lc; simpl_fv; my_set_solver).
      eapply msubst_preserves_basic_typing_tm; eauto.
      eapply tm_typing_regular_basic_typing in Ht.
      apply_eq Ht; eauto.
      cbn in He. subst.
      rewrite ctx_erase_app. f_equal. cbn.
      rewrite map_union_empty. eauto.
    }
    assert (closed_pty ∅ (m{Γv}p (-:ρ⤑[:T|A▶B]))). {
      eapply_eq msubst_preserves_closed_pty_empty; eauto using wf_pty_closed.
    }
    destruct ρ.
    + repeat msubst_simp. apply denotation_application_base_arg; eauto.
      auto_pose_fv x. repeat specialize_with x.
      intros v_x Hv_x.
      assert (ctxRst (Γ ++ [(x, {:B0|ϕ})]) (<[x := v_x]> Γv)) as HΓv'. {
        econstructor; eauto.
        econstructor; eauto using ctxRst_ok_ctx.
        sinvert HWF. sinvert H5. eauto.
        my_set_solver.
        msubst_simp.
      }
      specialize (HDe _ HΓv').
      rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
      rewrite <- msubst_intro_hty in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
      repeat msubst_simp.
    + repeat msubst_simp. apply denotation_application_arr_arg; eauto.
      qauto using pty_erase_msubst_eq.
      dup_hyp HWF (fun H => apply wf_pty_arr_not_in in H; destruct H as (L'&?)).
      auto_pose_fv x. repeat specialize_with x.
      intros v_x Hv_x.
      assert (ctxRst (Γ ++ [(x, -:ρ⤑[:T0|pre▶post] )]) (<[x := v_x]> Γv)) as HΓv'. {
        econstructor; eauto.
        econstructor; eauto using ctxRst_ok_ctx.
        sinvert HWF.
        apply wf_pty_closed. eauto.
        my_set_solver.
        msubst_simp.
      }
      specialize (HDe _ HΓv').
      rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
      assert ((m{<[x:=v_x]> Γv}h) ([:T|A▶B] ^h^ x) = m{Γv}h [:T|A▶B]) as Htmp3. {
        rewrite <- open_not_in_eq_hty.
        apply msubst_insert_fresh_hty; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
        eauto.
      }
      rewrite Htmp3 in HDe.
      repeat msubst_simp.

  (* [TLamFix] *)
  - intros Γ Tx ϕ e T A B L HWF Hlam HDlam Γv HΓv. repeat msubst_simp.
    eapply denotation_application_fixed. {
      econstructor. econstructor.
      instantiate_atom_listctx.
      eapply value_typing_regular_basic_typing in Hlam.
      eapply_eq msubst_preserves_basic_typing_value; eauto.
      apply_eq Hlam.
      rewrite ctx_erase_app. f_equal. cbn.
      rewrite map_union_empty. eauto.
      simpl. repeat msubst_simp.
      rewrite <- msubst_open_var_tm; eauto using ctxRst_closed_env, ctxRst_lc.
      simpl_fv; my_set_solver.
    } {
      eapply_eq msubst_preserves_closed_pty_empty; eauto using wf_pty_closed.
      repeat msubst_simp.
    }
    auto_pose_fv x. repeat specialize_with x.
    intros v_x Hv_x.
    assert (ctxRst (Γ ++ [(x, {:Tx|ϕ})]) (<[x := v_x]> Γv)) as HΓv'. {
      econstructor; eauto.
      econstructor; eauto using ctxRst_ok_ctx.
      sinvert HWF. sinvert H4. eauto.
      my_set_solver.
      msubst_simp.
    }
    specialize (HDlam _ HΓv').
    simpl in HDlam.
    repeat msubst_simp.
    assert ((m{<[x:=v_x]> Γv}q) b0:x≺ x = b0:v≺ v_x) as Hq. {
      change (b0:x≺ x) with ({1 ~q> x}(b0≺b1)).
      rewrite <- msubst_intro_qualifier by
          (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
      rewrite msubst_fresh_qualifier. reflexivity.
      my_set_solver.
    }
    rewrite Hq in HDlam.
    rewrite <- msubst_intro_tm in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite <- msubst_intro_am in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite <- msubst_intro_postam in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_qualifier in HDlam by
        (eauto using ctxRst_closed_env, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_am in HDlam by
        (eauto using ctxRst_closed_env, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_postam in HDlam by
        (eauto using ctxRst_closed_env, ptyR_closed_value;
         simpl_fv; my_set_solver).
    eauto.

  (* [TValue] *)
  - intros Γ v ρ _ HDv Γv HΓv. specialize (HDv _ HΓv).
    repeat msubst_simp. rewrite <- denotation_value_pure. auto.

  (* [TSub] *)
  - intros Γ e τ1 τ2 HWFτ2 _ HDτ1 Hsub Γv HΓv. specialize (HDτ1 _ HΓv).
    apply Hsub in HDτ1; auto.

  (* [TLetE] *)
  - intros Γ e_x e Tx A T Bx_ρx BxB_ρ Bx_ρx_B_ρ L HWFBρ HTe_x HDe_x Hin1 Hin2 Ht He Γv HΓv.
    split; [| split]. {
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      econstructor. eauto using tm_typing_regular_basic_typing.
      instantiate_atom_listctx.
      sinvert HWFBρ.
      simpl_Forall2.
      eapply tm_typing_regular_basic_typing in Ht; eauto.
      apply_eq Ht.
      cbn. rewrite ctx_erase_app_r by my_set_solver.
      repeat f_equal. apply tm_typing_regular_wf in HTe_x.
      sinvert HTe_x. eauto.
      cbn. by rewrite <- hty_erase_msubst_eq.
    } {
      eauto using msubst_preserves_closed_hty_empty, wf_hty_closed.
    }
    repeat msubst_simp.
    intros HBtyped α β v HDα Hstepv.
    apply reduction_tlete in Hstepv. destruct Hstepv as (βx & βe & v_x & Htmp & Hstepv_x & Hstepv).
    auto_pose_fv x. repeat specialize_with x.
    specialize (HDe_x _ HΓv). repeat msubst_simp.
    destruct HDe_x as (Hte_x & Hclosede_x & HDe_x).
    assert (amlist_typed ((m{Γv}pa) Bx_ρx) Tx) as HH1. {
      clear - Hclosede_x.
      sinvert Hclosede_x. sinvert H. eauto.
    }
    specialize (HDe_x HH1 _ _ _ HDα Hstepv_x).
    destruct HDe_x as (Bxi' & ρxi' & HinBx_ρx & Hβx & Hv_x).
    apply postam_msubst_in in HinBx_ρx; eauto using ctxRst_closed_env.
    destruct HinBx_ρx as (Bxi & ρxi & Htmp0 & Htmp1 & HinBx_ρx). subst.
    rewrite msubst_intro_tm with (x:=x) in Hstepv by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).

    assert (exists Bi ρi, In (Bxi, ρxi, Bi, ρi) Bx_ρx_B_ρ) as Hin. {
      simpl_Forall2.
      eauto.
    }
    destruct Hin as (Bi & ρi & Hin). clear Hin1.
    assert (In ((aconcat Bxi Bi), ρi) BxB_ρ) as Hinii. {
      simpl_Forall2.
      eauto.
    } clear Hin2.
    assert (ctxRst (Γ ++ [(x, ρxi)]) (<[x:=v_x]> Γv)) as HH2. {
      constructor; auto.
      econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.
      eapply tm_typing_regular_wf in HTe_x.
      sinvert HTe_x.
      qauto using wf_pty_closed.
    }
    specialize (He _ _ _ _ Hin _ HH2). repeat msubst_simp.
    destruct He as (Hte & Hclosede & He).
    assert (amlist_typed ((m{<[x:=v_x]> Γv}pa) [(Bi, ρi)]) T) as HH3. {
      apply msubst_amlist_typed.
      clear - HWFBρ Hinii.
      sinvert HWFBρ.
      hnf in *.
      qauto.
    }
    specialize (He HH3 (α ++ βx) βe v).
    assert ((a⟦(m{<[x:=v_x]> Γv}a) (aconcat A Bxi)⟧) (α ++ βx)) as Hconcat.
    { apply am_denotation_fv;
        eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
      repeat msubst_simp. apply am_concat; auto. } repeat msubst_simp.
    specialize (He Hconcat Hstepv). destruct He as (Bi'' & ρi'' & Hini & Hβe & Hv).
    apply postam_msubst_in in Hini; eauto using ctxRst_closed_env.
    destruct Hini as (Bi' & ρi' & Htmp0 & Htmp1 & Hini); subst.
    apply in_singleton in Hini. mydestr; subst.
    exists (m{<[x:=v_x]> Γv}a (aconcat Bxi Bi)), (m{<[x:=v_x]> Γv}p ρi).
    repeat split. 3: auto.
    + eapply_eq postam_in_msubst. eauto using ctxRst_closed_env. eauto.
      apply msubst_insert_fresh_postam; eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
    + repeat msubst_simp.
      apply am_concat; auto.
      apply am_denotation_fv; eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.

  (* [TApp] *)
  - intros Γ v1 v2 e ρ Tx A T Bx_ρx BxB_ρ Bx_ρx_B_ρ L HWF Hv2 HDv2 Hv1 HDv1 Hin1 Hin2 Ht He Γv HΓv.
    specialize (HDv1 _ HΓv). specialize (HDv2 _ HΓv).
    split; [| split]. {
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      econstructor.
      apply_eq value_typing_regular_basic_typing; eauto.
      apply_eq value_typing_regular_basic_typing; eauto.
      instantiate_atom_listctx.
      sinvert HWF.
      simpl_Forall2.
      eapply tm_typing_regular_basic_typing in Ht; eauto.
      apply_eq Ht.
      rewrite ctx_erase_app_r by my_set_solver.
      repeat f_equal. apply value_typing_regular_wf in Hv1.
      sinvert Hv1. rewrite <- pty_erase_open_eq. eauto.
      cbn. by rewrite <- hty_erase_msubst_eq.
    } {
      eauto using msubst_preserves_closed_hty_empty, wf_hty_closed.
    }
    repeat msubst_simp.
    intros HBtyped α β v HDα Hstepv.
    apply reduction_tletapp in Hstepv. destruct Hstepv as (βx & βe & v_x & Htmp & Hstepv_x & Hstepv).
    destruct HDv1 as (Hev1 & Htv1 & Hclosedv1 & HDv1).
    assert (amlist_typed ((m{Γv}pa) Bx_ρx) Tx) as HH1. {
      clear - Hclosedv1.
      sinvert Hclosedv1. sinvert H. eauto.
    }
    case_split.
    + assert (exists c : constant, (m{Γv}v) v2 = c) as Hc. {
        sinvert HDv2.
        eapply empty_basic_typing_base_const_exists.
        simp_hyps.
        sinvert H0. eauto.
      } destruct Hc as (c & Hev2).
      rewrite msubst_open_am in HDα by eauto using ctxRst_closed_env, ctxRst_lc.
      rewrite Hev2 in *.
      specialize (HDv1 HH1 _ HDv2 _ _ _ HDα Hstepv_x).
      destruct HDv1 as (Bxi' & ρxi' & HinBx_ρx & Hβx & Hv_x).
      apply postam_msubst_in in HinBx_ρx; eauto using ctxRst_closed_env.
      destruct HinBx_ρx as (Bxi & ρxi & Htmp0 & Htmp1 & HinBx_ρx). subst.
      auto_pose_fv x. repeat specialize_with x.
      rewrite msubst_intro_tm with (x:=x) in Hstepv by
          (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
           simpl_fv; my_set_solver).
      assert (exists Bi ρi, In (Bxi, ρxi, Bi, ρi) Bx_ρx_B_ρ) as Hin. {
        simpl_Forall2.
        eauto.
      }
      destruct Hin as (Bi & ρi & Hin). clear Hin1.
      assert (In ((aconcat (Bxi ^a^ v2) Bi), ρi) BxB_ρ) as Hinii. {
        simpl_Forall2.
        eauto.
      } clear Hin2.
      assert (ctxRst (Γ ++ [(x, ρxi ^p^ v2)]) (<[x:=v_x]> Γv)) as HH2. {
        constructor; auto.
        econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.

        clear - HΓv HinBx_ρx Hv1 Hv2 Hev2.
        assert (lc v2) as Hlc. {
          eauto using value_typing_regular_basic_typing, basic_typing_regular_tm.
        }
        eapply value_typing_regular_wf in Hv1.
        sinvert Hv1.
        auto_pose_fv x. repeat specialize_with x.
        eapply H8 in HinBx_ρx.
        eapply wf_pty_closed in HinBx_ρx.
        rewrite <- subst_intro_pty with (x:=x) by (eauto; my_set_solver).
        eapply subst_preserves_closed_pty; eauto.
        eapply msubst_constant_remove_arr_pty_ctx; eauto.

        rewrite <- Hev2 in *.
        rewrite <- msubst_open_pty in * by eauto using ctxRst_closed_env, ctxRst_lc.
        apply_eq Hv_x.
        apply ptyR_typed_closed in Hv_x.
        qauto.
      }
      specialize (He _ _ _ _ Hin _ HH2). repeat msubst_simp.
      destruct He as (Hte & Hclosede & He).
      assert (amlist_typed ((m{<[x:=v_x]> Γv}pa) [(Bi, ρi)]) T) as HH3. {
        apply msubst_amlist_typed.
        clear - HWF Hinii.
        sinvert HWF.
        hnf in *.
        qauto.
      }
      specialize (He HH3 (α ++ βx) βe v).
      rewrite <- Hev2 in *.
      rewrite <- msubst_open_am in * by eauto using ctxRst_closed_env, ctxRst_lc.
      assert ((a⟦(m{<[x:=v_x]> Γv}a) (aconcat (A ^a^ v2) (Bxi ^a^ v2))⟧) (α ++ βx)) as Hconcat.
      { apply am_denotation_fv;
          eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
        repeat msubst_simp.
        apply am_concat; auto.
      } repeat msubst_simp.
      specialize (He Hconcat Hstepv). destruct He as (Bi'' & ρi'' & Hini & Hβe & Hv).
      apply postam_msubst_in in Hini; eauto using ctxRst_closed_env.
      destruct Hini as (Bi' & ρi' & Htmp0 & Htmp1 & Hini); subst.
      apply in_singleton in Hini. mydestr; subst.
      exists (m{<[x:=v_x]> Γv}a (aconcat (Bxi ^a^ v2) Bi)), (m{<[x:=v_x]> Γv}p ρi).
      repeat split. 3: auto.
      * eapply_eq postam_in_msubst. eauto using ctxRst_closed_env. eauto.
        apply msubst_insert_fresh_postam; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
      * repeat msubst_simp.
        apply am_concat; auto.
        apply am_denotation_fv; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
    + pose proof Hv1 as HWFv1.
      apply value_typing_regular_wf in HWFv1.
      destruct ρ; msubst_simp. simplify_eq.
      dup_hyp HWFv1 (fun H => apply wf_pty_arr_not_in in H; destruct H as (L'&?)).
      auto_pose_fv x. repeat specialize_with x.
      rewrite <- (open_not_in_eq_am x) in * by my_set_solver.
      specialize (HDv1 HH1 _ HDv2 _ _ _ HDα Hstepv_x).
      destruct HDv1 as (Bxi' & ρxi' & HinBx_ρx & Hβx & Hv_x).
      apply postam_msubst_in in HinBx_ρx; eauto using ctxRst_closed_env.
      destruct HinBx_ρx as (Bxi & ρxi & Htmp0 & Htmp1 & HinBx_ρx). subst.
      rewrite msubst_intro_tm with (x:=x) in Hstepv by
          (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
           simpl_fv; my_set_solver).
      assert (exists Bi ρi, In (Bxi, ρxi, Bi, ρi) Bx_ρx_B_ρ) as Hin. {
        simpl_Forall2.
        eauto.
      }
      destruct Hin as (Bi & ρi & Hin). clear Hin1.
      assert (x ∉ stale (Bxi ^a^ x) ∪ stale (ρxi ^p^ x)) as Hfresh. {
        simpl in H. rewrite not_elem_of_union in H. destruct H as (_ & H).
        eapply postam_in_open in HinBx_ρx.
        eapply not_in_union_list in H; cycle 1.
        rewrite in_map_iff. eauto.
        my_set_solver.
      }
      assert (In ((aconcat Bxi Bi), ρi) BxB_ρ) as Hinii. {
        simpl_Forall2.
        rewrite <- (open_not_in_eq_am x) in * by my_set_solver.
        eauto.
      } clear Hin2.
      assert (ctxRst (Γ ++ [(x, ρxi)]) (<[x:=v_x]> Γv)) as HH2. {
        constructor; auto.
        econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.

        clear - HWFv1 Hfresh HinBx_ρx.
        sinvert HWFv1.
        auto_pose_fv x'. repeat specialize_with x'.
        eapply H8 in HinBx_ρx.
        rewrite <- (open_not_in_eq_pty x) in HinBx_ρx by my_set_solver.
        apply wf_pty_closed in HinBx_ρx.
        apply_eq HinBx_ρx.
        rewrite remove_arr_pty_ctx_dom_union.
        simpl. my_set_solver.

        apply_eq Hv_x.
        apply ptyR_typed_closed in Hv_x. intuition.
      }
      specialize (He _ _ _ _ Hin).
      rewrite <- (open_not_in_eq_pty x) in He by my_set_solver.
      rewrite <- (open_not_in_eq_am x) in He by my_set_solver.
      specialize (He _ HH2). repeat msubst_simp.
      destruct He as (Hte & Hclosede & He).
      assert (amlist_typed ((m{<[x:=v_x]> Γv}pa) [(Bi, ρi)]) T) as HH3. {
        apply msubst_amlist_typed.
        clear - HWF Hinii.
        sinvert HWF.
        hnf in *.
        qauto.
      }
      specialize (He HH3 (α ++ βx) βe v).
      assert ((a⟦(m{<[x:=v_x]> Γv}a) (aconcat A Bxi)⟧) (α ++ βx)) as Hconcat.
      { apply am_denotation_fv;
          eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv. my_set_solver.
        repeat msubst_simp. apply am_concat; auto. } repeat msubst_simp.
      specialize (He Hconcat Hstepv). destruct He as (Bi'' & ρi'' & Hini & Hβe & Hv).
      apply postam_msubst_in in Hini; eauto using ctxRst_closed_env.
      destruct Hini as (Bi' & ρi' & Htmp0 & Htmp1 & Hini); subst.
      apply in_singleton in Hini. mydestr; subst.
      exists (m{<[x:=v_x]> Γv}a (aconcat Bxi Bi)), (m{<[x:=v_x]> Γv}p ρi).
      repeat split. 3: auto.
      * eapply_eq postam_in_msubst. eauto using ctxRst_closed_env. eauto.
        apply msubst_insert_fresh_postam; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
      * repeat msubst_simp.
        apply am_concat; auto.
        apply am_denotation_fv; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.

  (* [TEffOp] *)
  - intros Γ op v2 e ϕx A T Bx_ρx opϕB_ρ ϕ_B_ρ L HWF Hv2 HDv2 HWFp Hbuiltin Hin1 Hin2 Ht He Γv HΓv.
    specialize (HDv2 _ HΓv).
    split; [| split]. {
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      econstructor.
      apply_eq value_typing_regular_basic_typing; eauto. eauto.
      instantiate_atom_listctx.
      sinvert HWF.
      simpl_Forall2.
      eapply tm_typing_regular_basic_typing in Ht; eauto.
      apply_eq Ht.
      rewrite ctx_erase_app_r by my_set_solver. eauto.
      cbn. by rewrite <- hty_erase_msubst_eq.
    } {
      eauto using msubst_preserves_closed_hty_empty, wf_hty_closed.
    }
    repeat msubst_simp.
    intros HBtyped α β v HDα Hstepv.
    apply reduction_tleteffop in Hstepv. destruct Hstepv as (c2 & c_x & β' & Htmp1 & Htmp2 & Htr & Hstepv).
    assert (amlist_typed ((m{Γv}pa) Bx_ρx) (ret_ty_of_op op)) as HH1. {
      clear - HWFp.
      sinvert HWFp. eauto using msubst_amlist_typed.
    }
    rewrite msubst_open_am in HDα by eauto using ctxRst_closed_env, ctxRst_lc.
    rewrite Htmp1 in *.
    hnf in HWFbuiltin.
    apply HWFbuiltin with (Γv:=Γv) in Hbuiltin; eauto.
    rename Hbuiltin into HDop.
    hnf in HDop. repeat msubst_simp.
    specialize (HDop _ HDv2 _ HDα _ Htr).
    destruct HDop as (Bxi' & ρxi' & HinBx_ρx & HDc_x).
    apply postam_msubst_in in HinBx_ρx; eauto using ctxRst_closed_env.
    destruct HinBx_ρx as (Bxi & ρxi & -> & -> & HinBx_ρx). subst.
    auto_pose_fv x. repeat specialize_with x.
    rewrite msubst_intro_tm with (x:=x) in Hstepv by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    assert (exists ϕ Bi ρi, Bxi = aϵ /\ ρxi = {:ret_ty_of_op op|ϕ} /\ In (ϕ, Bi, ρi) ϕ_B_ρ) as Hin. {
      simpl_Forall2.
      eauto 10.
    }
    destruct Hin as (ϕy & Bi & ρi & -> & -> & Hin). clear Hin1.
    assert (In ((aconcat (⟨op| b1:v= v2 & ϕy⟩) Bi), ρi) opϕB_ρ) as Hinii. {
      simpl_Forall2.
      eauto.
    } clear Hin2.
    assert (ctxRst (Γ ++ [(x, {:ret_ty_of_op op|ϕy} ^p^ v2)]) (<[x:=vconst c_x]> Γv)) as HH2. {
      constructor; auto.
      econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.
      assert (lc v2) as Hlc. {
        clear - Hv2.
        apply value_typing_regular_basic_typing in Hv2.
        apply basic_typing_regular_value in Hv2. eauto.
      }
      clear - HinBx_ρx HWFp HΓv Hlc Htmp1.
      sinvert HWFp.
      auto_pose_fv x. repeat specialize_with x.
      apply H8 in HinBx_ρx.
      eapply wf_pty_closed in HinBx_ρx.
      eapply subst_preserves_closed_pty in HinBx_ρx; eauto.
      rewrite subst_intro_pty in HinBx_ρx; eauto.
      my_set_solver.
      eapply msubst_constant_remove_arr_pty_ctx; eauto.

      clear - HDc_x HΓv Htmp1.
      rewrite msubst_open_pty by eauto using ctxRst_closed_env, ctxRst_lc.
      rewrite Htmp1. eauto.
    }
    specialize (He _ _ _ Hin _ HH2). repeat msubst_simp.
    destruct He as (Hte & Hclosede & He).
    assert (amlist_typed ((m{<[x:=vconst c_x]> Γv}pa) [(Bi, ρi)]) T) as HH3. {
      apply msubst_amlist_typed.
      clear - HWF Hinii.
      sinvert HWF.
      hnf in *.
      qauto.
    }
    specialize (He HH3 (α ++ [ev{op~c2:=c_x}]) β' v).
    feed specialize He; eauto. {
      apply am_concat; auto.
      rewrite <- Htmp1 in *.
      rewrite <- msubst_open_am in * by eauto using ctxRst_closed_env, ctxRst_lc.
      apply am_denotation_fv;
        eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
      (* Should be a lemma. *)
      split.
      (* lemma? *)
      econstructor.
      sinvert Hclosede. sinvert H1.
      sinvert H6. eauto.
      sinvert Hclosede. sinvert H1.
      simpl in H2.
      rewrite !union_subseteq in H2. simp_hyps.
      eauto.

      repeat esplit; eauto.
      apply ptyR_typed_closed in HDv2. simp_hyps. sinvert H1. eauto.
      sinvert HDc_x. simp_hyps. sinvert H1. eauto.

      rewrite !qualifier_and_open.
      apply denote_qualifier_and.
      rewrite !msubst_qualifier by eauto using ctxRst_closed_env.
      cbn. repeat msubst_simp.
      cbn. rewrite !decide_True by auto.
      cbn. rewrite !decide_False by auto.
      cbn. rewrite !decide_True by auto.
      rewrite_msubst_insert; eauto using ctxRst_closed_env, ptyR_closed_value.
      2: apply not_elem_of_dom; simpl_fv; my_set_solver.
      rewrite Htmp1. cbn. rewrite lookup_insert. cbn. intuition.
    }
    repeat msubst_simp.
    destruct He as (Bi'' & ρi'' & Hini & Hβe & Hv).
    apply postam_msubst_in in Hini; eauto using ctxRst_closed_env.
    destruct Hini as (Bi' & ρi' & -> & -> & Hini); subst.
    apply in_singleton in Hini. mydestr; subst.
    exists (m{<[x:=vconst c_x]> Γv}a (aconcat (⟨op|b1:v= v2 & ϕy⟩) Bi)), (m{<[x:=vconst c_x]> Γv}p ρi).
    repeat split. 3: auto.
    + eapply_eq postam_in_msubst. eauto using ctxRst_closed_env. eauto.
      apply msubst_insert_fresh_postam; eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
    + repeat msubst_simp.
      rewrite <- app_one_is_cons.
      apply am_concat; auto.
      apply am_denotation_fv; eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
      (* should be a lemma *)
      rewrite msubst_aevent; eauto using ctxRst_closed_env.
      cbn. cbn in HDc_x. simp_hyps.
      sinvert H0.
      sinvert H1.
      repeat msubst_simp.
      rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
      repeat msubst_simp. rewrite Htmp1.
      split.

      econstructor; eauto.
      clear - H5.
      sinvert H5.
      econstructor.
      instantiate_atom_listctx.
      rewrite !qualifier_and_open.
      apply lc_qualifier_and.
      cbn. rewrite decide_True by auto. cbn. repeat econstructor.
      rewrite open_swap_qualifier in *; eauto using lc.
      eauto using open_lc_respect_qualifier.

      simpl. rewrite qualifier_and_fv. simpl.
      simpl in H6. rewrite <- open_fv_qualifier' in H6.
      clear - H6.
      repeat my_set_solver.

      repeat esplit; eauto.
      apply ptyR_typed_closed in HDv2. simp_hyps. sinvert H1. eauto.
      rewrite !qualifier_and_open.
      apply denote_qualifier_and.
      split.
      cbn. cbn. rewrite decide_True by auto. cbn. eauto.
      eapply (H2 _ [] []). repeat econstructor.

  (* [TMatchb] *)
  - intros Γ v e1 e2 ϕ τ L HWFτ Htv HDv Hte1 HDe1 Hte2 HDe2 Γv HΓv.
    specialize (HDv _ HΓv).
    auto_pose_fv x. repeat specialize_with x.
    split; [| split]. {
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      econstructor.
      qauto using value_typing_regular_basic_typing.
      rewrite <- hty_erase_msubst_eq.
      eapply tm_typing_regular_basic_typing in Hte1.
      eapply basic_typing_strengthen_tm.
      rewrite <- ctx_erase_app_r.
      eauto. my_set_solver. my_set_solver.
      rewrite <- hty_erase_msubst_eq.
      eapply tm_typing_regular_basic_typing in Hte2.
      eapply basic_typing_strengthen_tm.
      rewrite <- ctx_erase_app_r.
      eauto. my_set_solver. my_set_solver.
    } {
      eauto using msubst_preserves_closed_hty_empty, wf_hty_closed.
    }
    destruct τ. repeat msubst_simp.
    intros HBtyped α β v' HDα Hstepv.
    assert ((m{Γv}v) v = true \/ (m{Γv}v) v = false) as Hv. {
      apply value_typing_regular_basic_typing in Htv.
      eapply msubst_preserves_basic_typing_value_empty in Htv; eauto.
      eapply empty_basic_typing_bool_value_exists in Htv.
      eauto.
    }
    destruct Hv as [Hv | Hv]; rewrite Hv in *.
    + apply reduction_matchb_true in Hstepv; mydestr; auto.
      assert (closed_pty (ctxdom ⦑Γ⦒) {:TBool|(b0:c=true) & ((b0:v=v) & ϕ)}) as Hc. {
        assert (lc v) as Hlc by
          eauto using value_typing_regular_basic_typing, basic_typing_regular_value.
        clear - Htv Hlc Hv HΓv.
        eapply value_typing_regular_wf in Htv.
        sinvert Htv. sinvert H1.
        econstructor. econstructor.
        sinvert H0.
        econstructor.
        intros. rewrite !qualifier_and_open.
        repeat apply lc_qualifier_and; eauto.
        repeat econstructor.
        repeat econstructor. by rewrite open_rec_lc_value.
        simpl. rewrite !qualifier_and_fv. simpl.
        eapply msubst_constant_remove_arr_pty_ctx in Hv; eauto.
        repeat my_set_solver.
      }
      assert (ctxRst (Γ ++ [(x, {:TBool|(b0:c=true) & ((b0:v=v) & ϕ)})]) (<[x:=vconst true]> Γv)) as HΓv'. {
        constructor; auto.
        econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.
        eauto.

        clear - Hv HDv HΓv Hc.
        eapply msubst_preserves_closed_pty_empty in Hc; eauto.
        repeat msubst_simp.
        simpl in HDv.
        simpl.
        simp_hyps.
        repeat (split; eauto).
        unfold bpropR in *.
        specialize (H2 _ _ _ H3).
        apply value_reduction_refl in H3. simp_hyps. subst.
        rewrite !qualifier_and_open.
        rewrite !denote_qualifier_and. repeat split; eauto.
        rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
        repeat msubst_simp. cbn. rewrite decide_True by auto. eauto.
        rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
        repeat msubst_simp. cbn. rewrite decide_True by auto.
        rewrite Hv. cbn. eauto.
      }
      specialize (HDe1 _ HΓv').
      msubst_simp.
      destruct HDe1 as (HTe1 & Hclosede1 & HDe1).
      rewrite msubst_insert_fresh_postam,
        msubst_insert_fresh_am,
        msubst_insert_fresh_tm in HDe1;
        eauto using ctxRst_closed_env; simpl_fv; my_set_solver.
    + apply reduction_matchb_false in Hstepv; mydestr; auto.
      assert (closed_pty (ctxdom ⦑Γ⦒) {:TBool|(b0:c=false) & ((b0:v=v) & ϕ)}) as Hc. {
        assert (lc v) as Hlc by
          eauto using value_typing_regular_basic_typing, basic_typing_regular_value.
        clear - Htv Hlc Hv HΓv.
        eapply value_typing_regular_wf in Htv.
        sinvert Htv. sinvert H1.
        econstructor. econstructor.
        sinvert H0.
        econstructor.
        intros. rewrite !qualifier_and_open.
        repeat apply lc_qualifier_and; eauto.
        repeat econstructor.
        repeat econstructor. by rewrite open_rec_lc_value.
        simpl. rewrite !qualifier_and_fv. simpl.
        eapply msubst_constant_remove_arr_pty_ctx in Hv; eauto.
        repeat my_set_solver.
      }
      assert (ctxRst (Γ ++ [(x, {:TBool|(b0:c=false) & ((b0:v=v) & ϕ)})]) (<[x:=vconst false]> Γv)) as HΓv'. {
        constructor; auto.
        econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.
        eauto.

        clear - Hv HDv HΓv Hc.
        eapply msubst_preserves_closed_pty_empty in Hc; eauto.
        repeat msubst_simp.
        simpl in HDv.
        simpl.
        simp_hyps.
        repeat (split; eauto).
        intros.
        unfold bpropR in *.
        specialize (H2 _ _ _ H3).
        apply value_reduction_refl in H3. simp_hyps. subst.
        rewrite !qualifier_and_open.
        rewrite !denote_qualifier_and. repeat split; eauto.
        rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
        repeat msubst_simp. cbn. rewrite decide_True by auto. eauto.
        rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
        repeat msubst_simp. cbn. rewrite decide_True by auto.
        rewrite Hv. cbn. eauto.
      }
      specialize (HDe2 _ HΓv').
      msubst_simp.
      destruct HDe2 as (HTe2 & Hclosede2 & HDe2).
      rewrite msubst_insert_fresh_postam,
        msubst_insert_fresh_am,
        msubst_insert_fresh_tm in HDe2;
        eauto using ctxRst_closed_env; simpl_fv; my_set_solver.
Qed.

Transparent msubst.

Definition valid_evop '(evop_ op argv retv) :=
  ∅ ⊢t argv ⋮v TNat /\ ∅ ⊢t retv ⋮v ret_ty_of_op op.

Definition valid_trace := Forall valid_evop.

Lemma valid_evop_any ev :
  valid_evop ev ->
  a⟦ ∘ ⟧ [ev].
Proof.
  intros H. split. repeat econstructor. my_set_solver.
  destruct ev. repeat esplit; qauto.
Qed.

Lemma valid_trace_any_star α :
  valid_trace α ->
  a⟦ astar ∘ ⟧ α.
Proof.
  intros H.
  split. repeat econstructor. my_set_solver.
  induction α. constructor.
  rewrite <- app_one_is_cons.
  sinvert H.
  econstructor; eauto using valid_evop_any.
Qed.

Corollary soundness :
  well_formed_builtin_typing ->
  forall (e : tm) T B,
    [] ⊢ e ⋮t [: T | astar ∘ ▶ B] ->
    forall α β (v : value),
      (* Alternatively, we can simply say [a⟦ astar ∘ ⟧ α]. *)
      valid_trace α ->
      α ⊧ e ↪*{ β } v ->
      exists Bi ρi, In (Bi, ρi) B /\
                 a⟦ Bi ⟧ β /\
                 p⟦ ρi ⟧ v.
Proof.
  intros HWFbuiltin **.
  apply fundamental with (Γv := ∅) in H; eauto using ctxRst.
  unfold msubst in *.
  rewrite !map_fold_empty in *.
  destruct H as (Ht & Hc & H).
  eapply H; eauto.
  sinvert Hc. sinvert H2. eauto.
  eauto using valid_trace_any_star.
Qed.

Print Assumptions soundness.
