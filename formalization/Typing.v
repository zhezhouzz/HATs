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
Definition wf_am (Γ: listctx pty) (A: am): Prop := closed_am (ctxdom Γ) A.

Definition prefix_am (Γ: listctx pty) (A B: am) : Prop :=
  forall Γv, ctxRst Γ Γv ->
        forall α, a⟦m{ Γv }a B⟧ α →
             a⟦m{ Γv }a A ;+ ∘*⟧ α.

Inductive wf_pty: listctx pty -> pty -> Prop :=
| wf_pty_base: forall Γ b ϕ,
    closed_pty (ctxdom Γ) {: b | ϕ } -> wf_pty Γ {: b | ϕ }
| wf_pty_arr: forall Γ ρ τ (L: aset),
    wf_pty Γ ρ ->
    (forall x, x ∉ L -> wf_hty (Γ ++ [(x, ρ)]) (τ ^h^ x)) ->
    wf_pty Γ (ρ ⇨ τ)
| wf_pty_ghost: forall Γ b ρ (L: aset),
    (forall x, x ∉ L -> wf_pty (Γ ++ [(x, mk_top b)]) (ρ ^p^ x)) ->
    wf_pty Γ (b ⇢ ρ)

with wf_hty: listctx pty -> hty -> Prop :=
| wf_hty_hoare: forall Γ ρ A B,
    wf_pty Γ ρ ->
    wf_am Γ A ->
    wf_am Γ B ->
    prefix_am Γ A B ->
    wf_hty Γ [: ρ | A ▶ B ]
| wf_hty_inter: forall Γ τ1 τ2,
    wf_hty Γ τ1 ->
    wf_hty Γ τ2 ->
    ⌊ τ1 ⌋ = ⌊ τ2 ⌋ ->
    wf_hty Γ (τ1 ⊓ τ2)
.

Notation " Γ '⊢WF' τ " := (wf_hty Γ τ) (at level 20, τ constr, Γ constr).
Notation " Γ '⊢WFp' τ " := (wf_pty Γ τ) (at level 20, τ constr, Γ constr).
Notation " Γ '⊢WFa' a " := (wf_am Γ a) (at level 20, a constr, Γ constr).

Reserved Notation "Γ '⊢' e '⋮t' τ" (at level 20).
Reserved Notation "Γ '⊢' e '⋮v' τ"  (at level 20).

(** Subtyping *)
Definition pty_subtyping (Γ: listctx pty) (ρ1 ρ2: pty) : Prop :=
  (* Assume [ρ1] and [ρ2] are valid [pty]s. *)
  ⌊ ρ1 ⌋ = ⌊ ρ2 ⌋ /\
  forall Γv, ctxRst Γ Γv ->
        forall e, p⟦m{ Γv }p ρ1⟧ e →
             p⟦m{ Γv }p ρ2⟧ e.

Definition subtyping (Γ: listctx pty) (τ1 τ2: hty) : Prop :=
  (* Assume [τ1] and [τ2] are valid [hty]s. *)
  ⌊ τ1 ⌋ = ⌊ τ2 ⌋ /\
  forall Γv, ctxRst Γ Γv ->
        forall e, ⟦m{ Γv }h τ1⟧ e →
             ⟦m{ Γv }h τ2⟧ e.

Notation " Γ '⊢' ρ1 '<⋮p' ρ2 " := (pty_subtyping Γ ρ1 ρ2) (at level 20, ρ1 constr, ρ2 constr, Γ constr).
Notation " Γ '⊢' τ1 '<⋮' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

(* The parameterized builtin typing relation (Δ). *)
Parameter builtin_typing_relation : effop -> pty -> Prop.

Reserved Notation "Γ '⊢' op '⋮o' ρ"  (at level 20).
Reserved Notation "Γ '⊢' e '⋮t' τ" (at level 20).
Reserved Notation "Γ '⊢' e '⋮v' ρ"  (at level 20).

(** Typing *)
Inductive effop_type_check : listctx pty -> effop -> pty -> Prop :=
| TEOp : forall Γ op ρ_op ρ,
    Γ ⊢WFp ρ ->
    builtin_typing_relation op ρ_op ->
    Γ ⊢ ρ_op <⋮p ρ ->
    ⌊ ρ ⌋ = ty_of_op op ->
    Γ ⊢ op ⋮o ρ
where
"Γ '⊢' op '⋮o' ρ" := (effop_type_check Γ op ρ).

Inductive term_type_check : listctx pty -> tm -> hty -> Prop :=
| TValue: forall Γ v ρ A,
    Γ ⊢WF [: ρ | A ▶ A] ->
    Γ ⊢ v ⋮v ρ ->
    Γ ⊢ v ⋮t [: ρ | A ▶ A]
| TSub: forall Γ e (τ1 τ2: hty),
    Γ ⊢WF τ2 ->
    Γ ⊢ e ⋮t τ1 ->
    Γ ⊢ τ1 <⋮ τ2 ->
    Γ ⊢ e ⋮t τ2
| TInter: forall Γ e (τ1 τ2: hty),
    Γ ⊢WF (τ1 ⊓ τ2) ->
    Γ ⊢ e ⋮t τ1 ->
    Γ ⊢ e ⋮t τ2 ->
    Γ ⊢ e ⋮t (τ1 ⊓ τ2)
| TLetE: forall Γ e_x e ρx ρ A A' B (L: aset),
    Γ ⊢WF [: ρ | A ▶ B ] ->
    Γ ⊢ e_x ⋮t [: ρx | A ▶ A' ] ->
    (forall x, x ∉ L ->
          (Γ ++ [(x, ρx)]) ⊢ (e ^t^ x) ⋮t [: ρ | A' ▶ B]) ->
    Γ ⊢ (tlete e_x e) ⋮t [: ρ | A ▶ B ]
| TApp: forall Γ (v1 v2: value) e ρ ρx ρ2 A A' B (L: aset),
    Γ ⊢WF [: ρ | (A ^a^ v2) ▶ B ] ->
    Γ ⊢ v2 ⋮v ρ2 ->
    Γ ⊢ v1 ⋮v (ρ2 ⇨ [: ρx | A ▶ A' ]) ->
    (forall x, x ∉ L ->
          (Γ ++ [(x, ρx ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: ρ | (A' ^a^ v2) ▶ B]) ->
    Γ ⊢ (tletapp v1 v2 e) ⋮t [: ρ | (A ^a^ v2) ▶ B ]
| TEffOp: forall Γ (op: effop) (v2: value) e ρ ρx ρ2 A A' B (L: aset),
    Γ ⊢WF [: ρ | (A ^a^ v2) ▶ B ] ->
    Γ ⊢ v2 ⋮v ρ2 ->
    Γ ⊢ op ⋮o (ρ2 ⇨ [: ρx | A ▶ A' ]) ->
    (forall x, x ∉ L ->
          (Γ ++ [(x, ρx ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: ρ | (A' ^a^ v2) ▶ B]) ->
    Γ ⊢ (tleteffop op v2 e) ⋮t [: ρ | (A ^a^ v2) ▶ B ]
| TMatchb: forall Γ (v: value) e1 e2 ϕ τ (L : aset),
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v {:TBool | ϕ} ->
    (* We can also directly encode the path condition without mentioning [x]:
    {: TNat | (qual [# v] (fun V => V !!! 0 = (cbool true))%fin) & ϕ ^q^ v} *)
    (forall x, x ∉ L -> (Γ ++ [(x, {: TBool | b0:c=true & b0:v= v & ϕ})]) ⊢ e1 ⋮t τ) ->
    (forall x, x ∉ L -> (Γ ++ [(x, {: TBool | b0:c=false & b0:v= v & ϕ})]) ⊢ e2 ⋮t τ) ->
    Γ ⊢ (tmatchb v e1 e2) ⋮t τ
with value_type_check : listctx pty -> value -> pty -> Prop :=
| TVSub: forall Γ (v: value) (ρ1 ρ2: pty),
    Γ ⊢WFp ρ2 ->
    Γ ⊢ v ⋮v ρ1 ->
    Γ ⊢ ρ1 <⋮p ρ2 ->
    Γ ⊢ v ⋮v ρ2
| TGhost: forall Γ v b ρ (L: aset),
    Γ ⊢WFp (b ⇢ ρ) ->
    (forall (x: atom), x ∉ L -> (Γ ++ [(x, mk_top b)]) ⊢ v ⋮v (ρ ^p^ x)) ->
    Γ ⊢ v ⋮v (b ⇢ ρ)
| TConstant: forall Γ (c: constant),
    Γ ⊢WFp (mk_eq_constant c) ->
    Γ ⊢ c ⋮v (mk_eq_constant c)
| TBaseVar: forall Γ (x: atom) b ϕ,
    Γ ⊢WFp (mk_eq_var b x) ->
    ctxfind Γ x = Some {: b | ϕ} ->
    Γ ⊢ x ⋮v (mk_eq_var b x)
| TFuncVar: forall Γ (x: atom) ρ τ,
    Γ ⊢WFp (ρ ⇨ τ) ->
    ctxfind Γ x = Some (ρ ⇨ τ) ->
    Γ ⊢ x ⋮v (ρ ⇨ τ)
| TLam: forall Γ Tx ρ e τ (L: aset),
    Γ ⊢WFp (ρ ⇨ τ) ->
    (forall x, x ∉ L -> (Γ ++ [(x, ρ)]) ⊢ (e ^t^ x) ⋮t (τ ^h^ x)) ->
    Tx = ⌊ ρ ⌋ ->
    Γ ⊢ (vlam Tx e) ⋮v (ρ ⇨ τ)
| TLamFix: forall Γ (Tx : base_ty) ϕ e τ T (L: aset),
    Γ ⊢WFp ({: Tx | ϕ} ⇨ τ) ->
    (* NOTE: should not open the whole type, because the first argument (bound
    variable 0) of the return type is not the fixed point function but [{: Tx |
    ϕ}]. The return type should be opened by [x]. *)
    (forall x, x ∉ L ->
          (Γ ++ [(x, {: Tx | ϕ})]) ⊢ (vlam (Tx ⤍ T) e) ^v^ x ⋮v (({: Tx | b0:x≺ x & ϕ} ⇨ τ) ⇨ (τ ^h^ x))) ->
    T = ⌊ τ ⌋ ->
    Γ ⊢ (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e)) ⋮v ({: Tx | ϕ} ⇨ τ)
where
"Γ '⊢' e '⋮t' τ" := (term_type_check Γ e τ) and "Γ '⊢' e '⋮v' ρ" := (value_type_check Γ e ρ).


Scheme value_term_type_check_ind := Minimality for value_type_check Sort Prop
    with term_value_type_check_ind := Minimality for term_type_check Sort Prop.
Combined Scheme value_term_type_check_mutind from
  value_term_type_check_ind, term_value_type_check_ind.

Lemma subtyping_preserves_basic_typing Γ τ1 τ2 :
  Γ ⊢ τ1 <⋮ τ2 ->
  ⌊τ1⌋ = ⌊τ2⌋.
Proof.
  qauto.
Qed.

Lemma pty_subtyping_preserves_basic_typing Γ ρ1 ρ2 :
  Γ ⊢ ρ1 <⋮p ρ2 ->
  ⌊ρ1⌋ = ⌊ρ2⌋.
Proof.
  qauto.
Qed.

Lemma effop_typing_preserves_basic_typing Γ ρ op :
  Γ ⊢ op ⋮o ρ ->
  ⌊ρ⌋ = ty_of_op op.
Proof.
  inversion 1; subst. eauto.
Qed.

Lemma value_typing_regular_wf : forall (Γ: listctx pty) (v: value) (ρ: pty),
    Γ ⊢ v ⋮v ρ -> wf_pty Γ ρ
with tm_typing_regular_wf : forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ -> wf_hty Γ τ.
Proof.
  all: destruct 1; eauto.
Qed.

Lemma value_tm_typing_regular_basic_typing:
  (forall (Γ: listctx pty) (v: value) (ρ: pty),
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋) /\
  (forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋).
Proof.
  apply value_term_type_check_mutind; intros; cbn; subst; eauto.
  - hauto using pty_subtyping_preserves_basic_typing.
  - auto_pose_fv x. repeat specialize_with x.
    rewrite ctx_erase_app_r in H1 by my_set_solver.
    rewrite <- pty_erase_open_eq in H1.
    eapply basic_typing_strengthen_value; eauto. my_set_solver.
  - econstructor.
    qauto using ctx_erase_lookup.
  - econstructor.
    qauto using ctx_erase_lookup.
  - econstructor.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H1 by my_set_solver.
    rewrite <- hty_erase_open_eq in H1.
    eauto.
  - econstructor.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H1 by my_set_solver.
    cbn in H1.
    rewrite <- hty_erase_open_eq in H1.
    eauto.
  - hauto using subtyping_preserves_basic_typing.
  - econstructor; eauto.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H3 by my_set_solver.
    eauto.
  - econstructor.
    cbn in H3. eauto. eauto.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H5 by my_set_solver.
    rewrite <- pty_erase_open_eq in H5.
    eauto.
  - apply effop_typing_preserves_basic_typing in H2. cbn in H2. sinvert H2.
    econstructor; eauto. qauto.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H4 by my_set_solver.
    rewrite <- pty_erase_open_eq in H4.
    rewrite <- H7. eauto.
  - auto_pose_fv x. repeat specialize_with x.
    rewrite ctx_erase_app_r in H3, H5 by my_set_solver.
    econstructor; eauto.
    eapply basic_typing_strengthen_tm; eauto. my_set_solver.
    eapply basic_typing_strengthen_tm; eauto. my_set_solver.
Qed.

Lemma value_typing_regular_basic_typing: forall (Γ: listctx pty) (v: value) (ρ: pty),
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋.
Proof.
  apply value_tm_typing_regular_basic_typing.
Qed.

Lemma tm_typing_regular_basic_typing: forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋.
Proof.
  apply value_tm_typing_regular_basic_typing.
Qed.

Lemma am_concat: forall A B α β,
    (a⟦A⟧) α -> (a⟦B⟧) β -> (a⟦ aconcat A B ⟧) (α ++ β).
Proof.
  intros.
  split.
  select! (a⟦_⟧ _) (fun H => apply langA_closed in H; sinvert H).
  repeat econstructor; eauto. my_set_solver.
  split.
  select! (a⟦_⟧ _) (fun H => apply langA_valid_trace in H).
  apply Forall_app. eauto.
  eauto.
Qed.

(* TODO: move everything [msubst]-related to another file, and [subst]-related
to the right files. *)
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
    m{Γv}h [:ρ|A▶B] = [:m{Γv}p ρ|m{Γv}a A ▶ m{Γv}a B].
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
  | H: context [ m{ _ }h [:_|_▶_] ] |- _ => rewrite msubst_hoarehty in H
  | |- context [ m{ _ }h [:_|_▶_] ] => rewrite msubst_hoarehty
  | H: context [ m{ _ }h (_⊓_) ] |- _ => rewrite msubst_interhty in H
  | |- context [ m{ _ }h (_⊓_) ] => rewrite msubst_interhty
  | H: context [ m{ _ }p (mk_top _) ] |- _ => rewrite msubst_mk_top in H
  | |- context [ m{ _ }p (mk_top _) ] => rewrite msubst_mk_top
  | H: context [ m{ _ }p (mk_eq_constant _) ] |- _ => rewrite msubst_mk_eq_constant in H
  | |- context [ m{ _ }p (mk_eq_constant _) ] => rewrite msubst_mk_eq_constant
  | H: context [ m{ _ }p (mk_eq_var _ ?x) ], H': _ !! ?x = Some ?v |- _ => rewrite msubst_mk_eq_var with (v:=v) in H
  | H': _ !! ?x = Some ?v |- context [ m{ _ }p (mk_eq_var _ ?x) ] => rewrite msubst_mk_eq_var with (v:=v)
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

Lemma ctxRst_insert_easy Γ env (x: atom) ρ (v: value):
    ctxRst Γ env ->
    x ∉ ctxdom Γ ->
    p⟦ m{ env }p ρ ⟧ v ->
    ctxRst (Γ ++ [(x, ρ)]) (<[ x := v ]> env).
Proof.
  intros. econstructor; eauto.
  econstructor; eauto using ctxRst_ok_ctx.
  apply ptyR_typed_closed in H1. simp_hyps.
  (* This should be a lemma similar to [msubst_preserves_closed_pty_empty], or
  we should strenghthen this lemma. But don't bother now as it is only used
  here. *)
  sinvert H2.
  econstructor. eauto using lc_msubst_pty, ctxRst_lc.
  rewrite fv_of_msubst_pty_closed in H4 by eauto using ctxRst_closed_env.
  rewrite ctxRst_dom in * by eauto.
  my_set_solver.
Qed.

Lemma wf_pty_closed Γ ρ :
  wf_pty Γ ρ ->
  closed_pty (ctxdom Γ) ρ
with wf_hty_closed Γ τ :
  wf_hty Γ τ ->
  closed_hty (ctxdom Γ) τ.
Proof.
  all: destruct 1; eauto; split;
    let go :=
      repeat select (_ ⊢WFp _) (fun H => apply wf_pty_closed in H; sinvert H);
      repeat select (_ ⊢WF _) (fun H => apply wf_hty_closed in H; sinvert H);
      repeat destruct select (_ ⊢WFa _);
      eauto in
    match goal with
    | |- lc_pty _ =>
        repeat econstructor; try instantiate_atom_listctx; go
    | |- lc_hty _ =>
        repeat econstructor; try instantiate_atom_listctx; go
    | |- _ =>
        simpl; auto_pose_fv x; repeat specialize_with x; go;
        rewrite <- ?open_fv_hty' in *;
        rewrite <- ?open_fv_pty' in *;
        rewrite ?ctxdom_app_union in *;
        my_set_solver
    end.
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
  generalize dependent e_x.
  induction H; intros; subst. easy.
  sinvert H.
  - ospecialize* IHmultistep; eauto.
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
  generalize dependent v2.
  generalize dependent v1.
  induction H; intros; subst. easy.
  simp_hyps. sinvert H.
  - eapply reduction_tlete in H0. simp_hyps.
    simplify_list_eq.
    eexists _, _, _. split; [| split]; eauto using reduction_letapplam'.
  - simplify_list_eq.
    ospecialize* H1; eauto. simp_hyps.
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

Lemma mk_top_closed_pty b : closed_pty ∅ (mk_top b).
Proof.
  econstructor. unshelve (repeat econstructor). exact ∅.
  my_set_solver.
Qed.

Lemma mk_top_denote_pty (b : base_ty) (v : value) :
  ∅ ⊢t v ⋮v b ->
  p⟦ mk_top b ⟧ v.
Proof.
  intros.
  split; [| split]; simpl; eauto using mk_top_closed_pty.
  hauto using value_reduction_refl.
Qed.

Lemma mk_eq_constant_closed_pty c : closed_pty ∅ (mk_eq_constant c).
Proof.
  econstructor. unshelve (repeat econstructor). exact ∅.
  my_set_solver.
Qed.

Lemma mk_eq_constant_denote_pty c:
  p⟦ mk_eq_constant c ⟧ c.
Proof.
  simpl. split; [| split]; cbn; eauto using mk_eq_constant_closed_pty.
  hauto using value_reduction_refl.
Qed.

Lemma closed_base_pty_qualifier_and B ϕ1 ϕ2 Γ:
  closed_pty Γ {: B | ϕ1 } ->
  closed_pty Γ {: B | ϕ2 } ->
  closed_pty Γ {: B | ϕ1 & ϕ2}.
Proof.
  intros [Hlc1 Hfv1] [Hlc2 Hfv2]. sinvert Hlc1. sinvert Hlc2.
  econstructor.
  econstructor. instantiate_atom_listctx.
  rewrite qualifier_and_open.
  eauto using lc_qualifier_and.
  simpl in *.
  rewrite qualifier_and_fv. my_set_solver.
Qed.

Lemma denote_base_pty_qualifier_and B ϕ1 ϕ2 ρ:
  p⟦ {: B | ϕ1 } ⟧ ρ ->
  p⟦ {: B | ϕ2 } ⟧ ρ ->
  p⟦ {: B | ϕ1 & ϕ2} ⟧ ρ.
Proof.
  intros (?&?&?) (?&?&?).
  split; [| split]; eauto using closed_base_pty_qualifier_and.
  intros.
  rewrite qualifier_and_open.
  rewrite denote_qualifier_and.
  qauto.
Qed.

Ltac rewrite_measure_irrelevant :=
  let t := (rewrite <- ?open_preserves_hty_measure,
                    <- ?open_preserves_pty_measure; lia) in
  match goal with
  | H : context [ptyR _ _ _] |- _ =>
      setoid_rewrite ptyR_measure_irrelevant' in H; [ | t .. ]
  | H : context [htyR _ _ _] |- _ =>
      setoid_rewrite htyR_measure_irrelevant' in H; [ | t .. ]
  | |- context [ptyR _ _ _] =>
      setoid_rewrite ptyR_measure_irrelevant'; [ | t .. ]
  | |- context [htyR _ _ _] =>
      setoid_rewrite htyR_measure_irrelevant'; [ | t .. ]
  end.

Lemma denotation_application_lam Tx T ρ τ e :
  Tx ⤍ T = ⌊ ρ⇨τ ⌋ ->
  ∅ ⊢t vlam Tx e ⋮t Tx ⤍ T ->
  closed_pty ∅ (ρ⇨τ) ->
  (forall (v_x : value),
      p⟦ρ⟧ v_x ->
      ⟦τ ^h^ v_x⟧ (e ^t^ v_x)) ->
  (p⟦ρ⇨τ⟧) (vlam Tx e).
Proof.
  intros He Ht Hc H.
  split; [| split]; eauto. sinvert He; eauto.
  intros v_x HDv_x.
  repeat rewrite_measure_irrelevant.
  specialize (H v_x HDv_x).
  eapply htyR_refine; cycle 1. eauto.

  apply ptyR_typed_closed in HDv_x. simp_hyps. sinvert H0.
  split; intros.
  - apply htyR_typed_closed in H. destruct H as [H _].
    repeat esplit. eauto.
    rewrite <- hty_erase_open_eq.
    sinvert He.
    eapply mk_app_e_v_has_type; eauto.
  - eapply reduction_letapplam; eauto using basic_typing_regular_value.
Qed.

Lemma denotation_application_fixed (Tx : base_ty) T ϕ τ e :
  T = ⌊ τ ⌋ ->
  ∅ ⊢t vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e) ⋮v Tx ⤍ T ->
  closed_pty ∅ ({:Tx|ϕ}⇨τ) ->
  (forall (v_x : value),
      p⟦{:Tx | ϕ}⟧ v_x ->
      p⟦({:Tx | (b0:v≺ v_x) & ϕ} ⇨ τ) ⇨ (τ ^h^ v_x)⟧
        ((vlam (Tx ⤍ T) e) ^v^ v_x)) ->
  p⟦{:Tx | ϕ}⇨τ⟧ (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e)).
Proof.
  intros He Ht Hc Hlam.
  split; [| split]; eauto. subst; eauto.
  intros v_x HDc.
  repeat rewrite_measure_irrelevant.
  assert (exists c, v_x = vconst c) as H. {
    apply ptyR_typed_closed in HDc.
    destruct HDc as [H _]. sinvert H.
    eauto using empty_basic_typing_base_const_exists.
  }
  destruct H as [c ->].
  induction c using (well_founded_induction constant_lt_well_founded).
  specialize (Hlam c HDc).
  destruct Hlam as (HTlam&HClam&HDlam).
  specialize (HDlam (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e))).
  repeat rewrite_measure_irrelevant.
  rewrite open_hty_idemp in HDlam by eauto using lc.
  eapply htyR_refine; cycle 1.
  apply HDlam.
  split; [| split].
  simpl. cbn. unfold erase, hty_erase_ in He. rewrite <- He. eauto.
  sinvert HClam. econstructor. sinvert H0. eauto. my_set_solver.
  intros v_y HDv_y.
  repeat rewrite_measure_irrelevant.
  assert (exists y, v_y = vconst y). {
    apply ptyR_typed_closed in HDv_y.
    destruct HDv_y as [HTv_y _]. sinvert HTv_y.
    eauto using empty_basic_typing_base_const_exists.
  }
  destruct H0 as (y&->).
  destruct HDv_y as (HTy&_&Hy).
  ospecialize* (Hy _ []); eauto. destruct Hy as [_ Hy].
  rewrite qualifier_and_open in Hy.
  rewrite denote_qualifier_and in Hy.
  simp_hyps.
  apply H; eauto.
  (* lemma? *)
  apply ptyR_typed_closed in HDc. simp_hyps.
  split; [| split]; eauto.
  intros. apply value_reduction_refl in H4. simp_hyps.
  intuition.

  split; intros.
  - subst. cbn in HTlam.
    repeat esplit.
    eapply mk_app_e_v_has_type; eauto.
    rewrite <- hty_erase_open_eq.
    eapply mk_app_e_v_has_type; eauto.
    apply ptyR_typed_closed in HDc. destruct HDc as [HTc _].
    sinvert HTc. eauto.
  - apply reduction_mk_app_e_v in H0.
    sinvert H0. sinvert H1. simplify_list_eq.
    apply reduction_mk_app_e_v' in H2.
    eauto.
    eauto using basic_typing_regular_value.
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

Lemma closed_hty_hoare_congr d ρ a b :
  closed_pty d ρ ->
  closed_am d a ->
  closed_am d b ->
  closed_hty d [: ρ | a ▶ b ].
Proof.
  inversion 1. inversion 1. inversion 1.
  econstructor.
  econstructor; eauto.
  simpl. my_set_solver.
Qed.

(* [fun x => leteffop y = op x in y] *)
Definition value_of_op op : value :=
  vlam TNat (tleteffop op (vbvar 0) (vbvar 0)).

Definition well_formed_builtin_typing :=
  forall op ρ,
    builtin_typing_relation op ρ ->
    p⟦ ρ ⟧ (value_of_op op).

Lemma msubst_value_of_op Γv op :
  m{Γv}v (value_of_op op) = value_of_op op.
Proof.
  rewrite msubst_fresh_value. eauto.
  my_set_solver.
Qed.

Lemma value_of_op_regular_basic_typing op:
  ∅ ⊢t value_of_op op ⋮v ty_of_op op.
Proof.
  econstructor.
  simpl. instantiate (1:=∅). intros.
  econstructor. econstructor. simplify_map_eq. reflexivity. reflexivity.
  instantiate_atom_listctx.
  simpl. econstructor. econstructor. simplify_map_eq. reflexivity.
Qed.

(* At some point the proof is very slow without marking [msubst] opaque. *)
Opaque msubst.

Ltac simpl_fv :=
  do_hyps (fun H => try match type of H with
                    | _ ∉ _ =>
                        simpl in H; rewrite ?ctxRst_dom in H by eassumption
                    end).

Lemma builtin_fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx pty) (op: effop) (ρ : pty),
    Γ ⊢ op ⋮o ρ ->
    forall Γv, ctxRst Γ Γv -> p⟦ m{ Γv }p ρ ⟧ (value_of_op op).
Proof.
  intros HWF Γ op ρ Hop Γv HΓv. sinvert Hop.
  apply H1; eauto.
  apply HWF in H0.
  rewrite msubst_fresh_pty; eauto.
  apply ptyR_typed_closed in H0. simp_hyps.
  sinvert H3.
  my_set_solver.
Qed.

Theorem fundamental_combined:
  well_formed_builtin_typing ->
  (forall (Γ: listctx pty) (v: value) (ρ: pty),
    Γ ⊢ v ⋮v ρ ->
    forall Γv, ctxRst Γ Γv -> p⟦ m{Γv}p ρ ⟧ (m{Γv}v v)) /\
  (forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ ->
    forall Γv, ctxRst Γ Γv -> ⟦ m{ Γv }h τ ⟧ (m{ Γv }t e)).
Proof.
  intros HWFbuiltin.
  apply value_term_type_check_mutind.
  (* [TVSub] *)
  - intros Γ v ρ1 ρ2 HWFρ2 _ HDρ1 Hsub Γv HΓv. specialize (HDρ1 _ HΓv).
    apply Hsub in HDρ1; auto.
  (* [TGhost] *)
  - intros Γ v b ρ L HWF Hv HDv Γv HΓv. repeat msubst_simp.
    split; [| split]. {
      assert (Γ ⊢ v ⋮v (b⇢ρ)) by eauto using value_type_check.
      eapply value_typing_regular_basic_typing in H.
      eapply msubst_preserves_basic_typing_value_empty in H; eauto.
      econstructor. apply_eq H. cbn. apply pty_erase_msubst_eq.
    } {
      eapply_eq msubst_preserves_closed_pty_empty; eauto using wf_pty_closed.
      msubst_simp.
    }
    auto_pose_fv x. repeat specialize_with x.
    intros.
    assert (ctxRst (Γ ++ [(x, mk_top b)]) (<[x:=v0]> Γv)) as HΓv'. {
      eapply ctxRst_insert_easy; eauto. my_set_solver.
      repeat msubst_simp. eauto using mk_top_denote_pty.
    }
    ospecialize* HDv; eauto.
    rewrite <- msubst_intro_pty in HDv by
      (eauto using ctxRst_closed_env, ctxRst_lc, basic_typing_closed_value;
       simpl_fv; my_set_solver).
    apply_eq HDv. by rewrite <- open_preserves_pty_measure.
    rewrite msubst_insert_fresh_value by
      (eauto using ctxRst_closed_env, basic_typing_closed_value;
       simpl_fv; my_set_solver).
    auto.
  (* [TConstant] *)
  - intros Γ c HWF Γv HΓv. repeat msubst_simp. eauto using mk_eq_constant_denote_pty.
  (* [TBaseVar] *)
  - intros Γ x b ϕ Hwf Hfind Γv HΓv.
    dup_hyp HΓv (fun H => eapply ctxRst_ctxfind in H; eauto). simp_hyps.
    repeat msubst_simp. rewrite H0.
    destruct H1 as [H _].
    sinvert H. cbn in H3.
    dup_hyp H3 (fun H => apply empty_basic_typing_base_const_exists in H).
    simp_hyps. subst. sinvert H3.
    eauto using mk_eq_constant_denote_pty.
  (* [TFuncVar] *)
  - intros Γ x ρ τ Hwf Hfind Γv HΓv.
    dup_hyp HΓv (fun H => eapply ctxRst_ctxfind in H; eauto). simp_hyps.
    repeat msubst_simp.
    by rewrite H0.
  (* [TLam] *)
  - intros Γ Tx ρ e τ L HWF Ht HDe He Γv HΓv. repeat msubst_simp.
    eapply denotation_application_lam; eauto.
    cbn. rewrite <- pty_erase_msubst_eq, <- hty_erase_msubst_eq. subst. eauto.
    {
      assert (Γ ⊢ vlam Tx e ⋮v (ρ⇨τ)) by eauto using value_type_check.
      eapply value_typing_regular_basic_typing in H.
      eapply msubst_preserves_basic_typing_value_empty in H; eauto.
      repeat msubst_simp.
      econstructor. apply_eq H. cbn. subst. reflexivity.
    } {
      eapply_eq msubst_preserves_closed_pty_empty; eauto using wf_pty_closed.
      msubst_simp.
    }
    intros v_x Hv_x.
    auto_pose_fv x. repeat specialize_with x.
    assert (ctxRst (Γ ++ [(x, ρ)]) (<[x:=v_x]> Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
    }
    ospecialize* HDe; eauto.
    rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite <- msubst_intro_hty in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    eauto.
  (* [TLamFix] *)
  - intros Γ Tx ϕ e τ T L HWF Hlam HDlam He Γv HΓv. repeat msubst_simp.
    eapply denotation_application_fixed; eauto.
    by rewrite <- hty_erase_msubst_eq.
    {
      assert (Γ ⊢ vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e) ⋮v ({:Tx|ϕ}⇨τ))
        by eauto using value_type_check.
      eapply value_typing_regular_basic_typing in H.
      eapply msubst_preserves_basic_typing_value_empty in H; eauto.
      repeat msubst_simp.
      apply_eq H. cbn. subst. eauto.
    } {
      eapply_eq msubst_preserves_closed_pty_empty; eauto using wf_pty_closed.
      repeat msubst_simp.
    }
    intros v_x Hv_x.
    auto_pose_fv x. repeat specialize_with x.
    assert (ctxRst (Γ ++ [(x, {:Tx|ϕ})]) (<[x:=v_x]> Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
      msubst_simp.
    }
    ospecialize* HDlam; eauto.
    rewrite <- msubst_intro_value in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    repeat msubst_simp.
    rewrite <- msubst_intro_hty in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_hty in HDlam by
      (eauto using ctxRst_closed_env, ptyR_closed_value; simpl_fv; my_set_solver).
    rewrite_msubst msubst_qualifier in HDlam.
    rewrite msubst_insert_fresh_qualifier in HDlam by
      (eauto using ctxRst_closed_env, ptyR_closed_value; simpl_fv; my_set_solver).
    apply_eq HDlam.
    simpl. repeat msubst_simp.
    clear. simplify_map_eq. eauto.
  (* [TValue] *)
  - intros Γ v ρ A HWF Hv HDv Γv HΓv. specialize (HDv _ HΓv).
    repeat msubst_simp.
    split; [| split]. {
      eapply value_typing_regular_basic_typing in Hv.
      eapply msubst_preserves_basic_typing_value_empty in Hv; eauto.
      cbn. rewrite <- pty_erase_msubst_eq. eauto.
    } {
      eapply_eq msubst_preserves_closed_hty_empty; eauto using wf_hty_closed.
      repeat msubst_simp.
    }
    intros. rewrite_measure_irrelevant.
    apply value_reduction_refl in H0. simp_hyps. subst. simpl_list. eauto.
  (* [TSub] *)
  - intros Γ e τ1 τ2 HWFτ2 _ HDτ1 Hsub Γv HΓv. specialize (HDτ1 _ HΓv).
    apply Hsub in HDτ1; auto.
  (* [TInter] *)
  - intros Γ e τ1 τ2 HWF HT1 HD1 HT2 HD2 Γv HΓv. repeat msubst_simp.
    split; [| split]. {
      eapply tm_typing_regular_basic_typing in HT1.
      eapply msubst_preserves_basic_typing_tm_empty in HT1; eauto.
      cbn. rewrite <- hty_erase_msubst_eq. eauto.
    } {
      eapply_eq msubst_preserves_closed_hty_empty; eauto using wf_hty_closed.
      repeat msubst_simp.
    }
    repeat rewrite_measure_irrelevant. eauto.
  (* [TLetE] *)
  - intros Γ e_x e ρx ρ A A' B L HWF HTe_x HDe_x HTe HDe Γv HΓv.
    ospecialize* HDe_x; eauto. repeat msubst_simp.
    split; [| split]. {
      assert (Γ ⊢ tlete e_x e ⋮t [:ρ|A▶B]) by eauto using term_type_check.
      eapply tm_typing_regular_basic_typing in H.
      eapply msubst_preserves_basic_typing_tm_empty in H; eauto.
      repeat msubst_simp.
      apply_eq H. cbn. eauto using pty_erase_msubst_eq.
    } {
      eapply_eq msubst_preserves_closed_hty_empty; eauto using wf_hty_closed.
      repeat msubst_simp.
    }
    intros α β v HDα Hstepv.
    apply reduction_tlete in Hstepv.
    destruct Hstepv as (βx & βe & v_x & -> & Hstepv_x & Hstepv).
    auto_pose_fv x. repeat specialize_with x.
    destruct HDe_x as (_ & _ & HDe_x).
    ospecialize* HDe_x; eauto. destruct HDe_x as [HDv_x HDα_βx].
    assert (ctxRst (Γ ++ [(x, ρx)]) (<[x:=v_x]> Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
    }
    ospecialize* HDe; eauto.
    rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    repeat msubst_simp.
    destruct HDe as (_ & _ & HDe).
    rewrite msubst_insert_fresh_am in HDe by
      (eauto using ctxRst_closed_env, ptyR_closed_value;
       simpl_fv; my_set_solver).
    ospecialize* HDe; eauto.
    repeat rewrite_measure_irrelevant.
    rewrite msubst_insert_fresh_pty in HDe by
      (eauto using ctxRst_closed_env, ptyR_closed_value;
       simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_am in HDe by
      (eauto using ctxRst_closed_env, ptyR_closed_value;
       simpl_fv; my_set_solver).
    clear - HDe.
    by simplify_list_eq.
  (* [TApp] *)
  - intros Γ v1 v2 e ρ ρx ρ2 A A' B L HWF HTv2 HDv2 HTv1 HDv1 HTe HDe Γv HΓv.
    ospecialize* HDv1; eauto. ospecialize* HDv2; eauto. repeat msubst_simp.
    split; [| split]. {
      assert (Γ ⊢ tletapp v1 v2 e ⋮t [:ρ|(A^a^v2)▶B]) by eauto using term_type_check.
      eapply tm_typing_regular_basic_typing in H.
      eapply msubst_preserves_basic_typing_tm_empty in H; eauto.
      repeat msubst_simp.
      apply_eq H. cbn. eauto using pty_erase_msubst_eq.
    } {
      eapply_eq msubst_preserves_closed_hty_empty; eauto using wf_hty_closed.
      repeat msubst_simp.
    }
    intros α β v HDα Hstepv.
    apply reduction_tletapp in Hstepv.
    destruct Hstepv as (βx & βe & v_x & -> & Hstepv_x & Hstepv).
    auto_pose_fv x. repeat specialize_with x.
    destruct HDv1 as (_ & _ & HDapp).
    repeat rewrite_measure_irrelevant.
    ospecialize* HDapp; eauto.
    destruct HDapp as (_ & _ & HDapp). simpl in HDapp.
    rewrite <- !msubst_open_am in HDapp by
        (eauto using ctxRst_closed_env, ctxRst_lc).
    rewrite <- !msubst_open_pty in HDapp by
        (eauto using ctxRst_closed_env, ctxRst_lc).
    ospecialize* HDapp; eauto.
    destruct HDapp as [HDv_x HDα_βx].
    assert (ctxRst (Γ ++ [(x, ρx ^p^ v2)]) (<[x:=v_x]> Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
    }
    ospecialize* HDe; eauto.
    rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    repeat msubst_simp.
    destruct HDe as (_ & _ & HDe).
    rewrite msubst_insert_fresh_am in HDe;
      eauto using ctxRst_closed_env, ptyR_closed_value.
    2 : {
      apply not_elem_of_union. split.
      simpl_fv; my_set_solver.
      eapply not_elem_of_weaken. 2: eauto using open_fv_am.
      my_set_solver.
    }
    ospecialize* HDe; eauto.
    repeat rewrite_measure_irrelevant.
    rewrite msubst_insert_fresh_pty in HDe by
      (eauto using ctxRst_closed_env, ptyR_closed_value;
       simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_am in HDe by
      (eauto using ctxRst_closed_env, ptyR_closed_value;
       simpl_fv; my_set_solver).
    clear - HDe.
    by simplify_list_eq.
  (* [TEffOp] *)
  - intros Γ op v2 e ρ ρx ρ2 A A' B L HWF HTv2 HDv2 HTop HTe HDe Γv HΓv.
    assert (∅ ⊢t (m{Γv}t) (tleteffop op v2 e) ⋮t ⌊ρ⌋) as HT. {
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      apply_eq tm_typing_regular_basic_typing; eauto using term_type_check.
    }
    assert (∅ ⊢t (m{Γv}t) (tletapp (value_of_op op) v2 e) ⋮t ⌊ρ⌋) as HTapp. {
      repeat msubst_simp. rewrite msubst_value_of_op.
      clear - HT.
      sinvert HT. sinvert H5.
      econstructor; eauto.
      econstructor. instantiate_atom_listctx.
      econstructor; eauto. econstructor. by simplify_map_eq.
      instantiate_atom_listctx. simpl.
      econstructor. econstructor. by simplify_map_eq.
    }
    eapply (htyR_refine _ (m{Γv}t (tletapp (value_of_op op) v2 e))). {
      split; eauto.
      repeat msubst_simp. rewrite msubst_value_of_op.
      assert (body ((m{Γv}t) e)) as Hbody. {
        sinvert HT. eexists. eauto using basic_typing_regular_tm.
      }
      clear - Hbody. intros * Hstepv.
      apply reduction_tleteffop in Hstepv.
      destruct Hstepv as (c2 & c_x & β' & -> & -> & Hred & Hstepv).
      eapply_eq multistep_step. econstructor; eauto using lc.
      unshelve (repeat econstructor); exact ∅.
      econstructor. simpl. econstructor; eauto.
      econstructor; eauto. by simplify_list_eq.
      simpl. econstructor. econstructor; solve [eauto].
      by simplify_list_eq. by simplify_list_eq.
    }

    eapply builtin_fundamental in HTop; eauto.
    rewrite <- (msubst_value_of_op Γv) in HTop.
    revert HTapp HTop. generalize (value_of_op op) as v1.
    intros v1 HTapp HDv1.
    ospecialize* HDv2; eauto. repeat msubst_simp.
    split; [| split]. {
      cbn. by rewrite <- pty_erase_msubst_eq.
    } {
      eapply_eq msubst_preserves_closed_hty_empty; eauto using wf_hty_closed.
      repeat msubst_simp.
    }
    (* The rest of the proof is exactly the same as [TApp]. Maybe find a way to
    abstract this and avoid copy-pasting. *)
    intros α β v HDα Hstepv.
    apply reduction_tletapp in Hstepv.
    destruct Hstepv as (βx & βe & v_x & -> & Hstepv_x & Hstepv).
    auto_pose_fv x. repeat specialize_with x.
    destruct HDv1 as (_ & _ & HDapp).
    repeat rewrite_measure_irrelevant.
    ospecialize* HDapp; eauto.
    destruct HDapp as (_ & _ & HDapp). simpl in HDapp.
    rewrite <- !msubst_open_am in HDapp by
        (eauto using ctxRst_closed_env, ctxRst_lc).
    rewrite <- !msubst_open_pty in HDapp by
        (eauto using ctxRst_closed_env, ctxRst_lc).
    ospecialize* HDapp; eauto.
    destruct HDapp as [HDv_x HDα_βx].
    assert (ctxRst (Γ ++ [(x, ρx ^p^ v2)]) (<[x:=v_x]> Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
    }
    ospecialize* HDe; eauto.
    rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    repeat msubst_simp.
    destruct HDe as (_ & _ & HDe).
    rewrite msubst_insert_fresh_am in HDe;
      eauto using ctxRst_closed_env, ptyR_closed_value.
    2 : {
      apply not_elem_of_union. split.
      simpl_fv; my_set_solver.
      eapply not_elem_of_weaken. 2: eauto using open_fv_am.
      my_set_solver.
    }
    ospecialize* HDe; eauto.
    repeat rewrite_measure_irrelevant.
    rewrite msubst_insert_fresh_pty in HDe by
      (eauto using ctxRst_closed_env, ptyR_closed_value;
       simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_am in HDe by
      (eauto using ctxRst_closed_env, ptyR_closed_value;
       simpl_fv; my_set_solver).
    clear - HDe.
    by simplify_list_eq.
  (* [TMatchb] *)
  - intros Γ v e1 e2 ϕ τ L HWF HTv HDv HTe1 HDe1 HTe2 HDe2 Γv HΓv.
    assert (∅ ⊢t (m{Γv}t) (tmatchb v e1 e2) ⋮t ⌊τ⌋) as HT by
      qauto using term_type_check,
                  tm_typing_regular_basic_typing,
                  msubst_preserves_basic_typing_tm_empty.
    auto_pose_fv x. repeat specialize_with x.
    ospecialize* HDv; eauto.
    repeat msubst_simp.
    assert (exists (b : bool), m{Γv}v v = b) as [b He] by
        qauto using value_typing_regular_basic_typing,
                    msubst_preserves_basic_typing_value_empty,
                    empty_basic_typing_bool_value_exists.
    rewrite He in *.
    assert (ctxRst
              (Γ ++ [(x, {:TBool|(b0:c=b) & ((b0:v=v) & ϕ)})])
              (<[x:=vconst b]>Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
      repeat msubst_simp.
      repeat apply denote_base_pty_qualifier_and; eauto.
      apply_eq mk_eq_constant_denote_pty. clear - HΓv.
      rewrite_msubst msubst_qualifier. simpl. repeat msubst_simp.
      apply_eq mk_eq_constant_denote_pty. clear - He HΓv.
      rewrite_msubst msubst_qualifier. simpl. rewrite He. repeat msubst_simp.
    }

    destruct b.
    + ospecialize* HDe1; eauto.
      rewrite msubst_insert_fresh_tm in HDe1 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_hty in HDe1 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      eapply htyR_refine; eauto.
      split; eauto using reduction_matchb_true.
      repeat esplit; eauto.
      apply htyR_typed_closed in HDe1. destruct HDe1 as [HTe1' _].
      rewrite <- hty_erase_msubst_eq in HTe1'. eauto.
    + ospecialize* HDe2; eauto.
      rewrite msubst_insert_fresh_tm in HDe2 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_hty in HDe2 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      eapply htyR_refine; eauto.
      split; eauto using reduction_matchb_false.
      repeat esplit; eauto.
      apply htyR_typed_closed in HDe2. destruct HDe2 as [HTe2' _].
      rewrite <- hty_erase_msubst_eq in HTe2'. eauto.
Qed.

Theorem fundamental_value:
  well_formed_builtin_typing ->
  forall (Γ: listctx pty) (v: value) (ρ: pty),
    Γ ⊢ v ⋮v ρ ->
    forall Γv, ctxRst Γ Γv -> p⟦ m{Γv}p ρ ⟧ (m{Γv}v v).
Proof.
  qauto using fundamental_combined.
Qed.

Theorem fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ ->
    forall Γv, ctxRst Γ Γv -> ⟦ m{ Γv }h τ ⟧ (m{ Γv }t e).
Proof.
  qauto using fundamental_combined.
Qed.

Transparent msubst.

Corollary soundness' :
  well_formed_builtin_typing ->
  forall (e : tm) (ρ : pty) (A : am),
    [] ⊢ e ⋮t [:ρ | A ▶ A] ->
    forall (v : value) α α',
      a⟦ A ⟧ α ->
      α ⊧ e ↪*{ α' } v ->
      p⟦ ρ ⟧ v /\ a⟦ A ⟧ (α ++ α').
Proof.
  intros HWF * HT * HDα Hstepv.
  eapply fundamental in HT; eauto using ctxRst.
  unfold msubst in HT. rewrite !map_fold_empty in HT.
  qauto using HT.
Qed.

Corollary soundness :
  well_formed_builtin_typing ->
  forall (v_f: value) (Bx By: base_ty) (ρ: pty) (A: am),
    [] ⊢ v_f ⋮v (Bx⇢(mk_top By)⇨[:ρ | A ▶ A]) ->
    forall v_x v_y,
      ∅ ⊢t v_x ⋮v Bx ->
      ∅ ⊢t v_y ⋮v By ->
      forall (v : value) α α',
        a⟦ {0 ~a> v_y} ({1 ~a> v_x} A) ⟧ α ->
        α ⊧ (mk_app_e_v v_f v_y) ↪*{ α' } v ->
        p⟦ {0 ~p> v_y} ({1 ~p> v_x} ρ) ⟧ v /\
          a⟦ {0 ~a> v_y} ({1 ~a> v_x} A) ⟧ (α ++ α').
Proof.
  intros HWF * HT * HTv_x HTv_y * HDα Hstepv.
  eapply fundamental_value in HT; eauto using ctxRst.
  unfold msubst in HT. rewrite !map_fold_empty in HT.
  destruct HT as (_&_&HD); eauto.
  repeat rewrite_measure_irrelevant.
  specialize (HD _ HTv_x).
  simpl pty_open in HD.
  destruct HD as (_&_&HD).
  repeat rewrite_measure_irrelevant.
  eapply HD; eauto using mk_top_denote_pty.
Qed.

Print Assumptions soundness.
