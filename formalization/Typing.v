From stdpp Require Import mapset.
From stdpp Require Import natmap.
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
Import Equation.
Import OperationalSemantics.
Import BasicTyping.
Import RefinementType.
Import Denotation.
Import Instantiation.
Import Substitution.

(* TODO: wf_am? *)

(** Well-formedness *)
Inductive wf_pty: listctx pty -> pty -> Prop :=
| wf_pty_base: forall Γ b ϕ,
    closed_pty (ctxdom ⦑ Γ ⦒) {v: b | ϕ } ->  wf_pty Γ {v: b | ϕ }
| wf_pty_arr: forall Γ ρ T A B (L: aset),
    (* NOTE: ρ? *)
    amlist_typed B T ->
    (forall x, x ∉ L ->
          (forall Bi ρi, In (Bi, ρi) B ->
                    wf_pty (Γ ++ [(x, ρ)]) ρi
          )
    ) ->
    wf_pty Γ (-: ρ ⤑[: T | A ⇒ B ]).

Inductive wf_hty: listctx pty -> hty -> Prop :=
| wf_hty_: forall Γ T A B,
    amlist_typed B T ->
    (forall Bi ρi, In (Bi, ρi) B ->
              wf_pty Γ ρi
    ) ->
    wf_hty Γ [: T | A ⇒ B ].

Notation " Γ '⊢WF' τ " := (wf_hty Γ τ) (at level 20, τ constr, Γ constr).
Notation " Γ '⊢WFp' τ " := (wf_pty Γ τ) (at level 20, τ constr, Γ constr).

Definition subtyping (Γ: listctx pty) (τ1 τ2: hty) : Prop :=
  (* Assume [τ1] and [τ2] are valid [hty]s. *)
  forall env, ctxRst Γ env ->
  (* NOTE: why not use value? *)
         forall e, ⟦ msubst hty_subst env τ1 ⟧ (tm_msubst env e) ->
              ⟦ msubst hty_subst env τ2 ⟧ (tm_msubst env e).

Notation " Γ '⊢' τ1 '⪡' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Reserved Notation "Γ '⊢' e '⋮t' τ" (at level 20).
Reserved Notation "Γ '⊢' e '⋮v' τ"  (at level 20).

Definition A_ρa_B_ρb_list_A_ρa (l: list (am * pty) ) (tril: list (am * pty * am * pty)) :=
  forall A ρa, In (A, ρa) l <-> (exists B ρb, In (A, ρa, B, ρb) tril).

Definition A_ρa_B_ρb_list_AB_ρb (l: list (am * pty) ) (tril: list (am * pty * am * pty)) :=
  forall A B ρb, In (aconcat A B, ρb) l <-> (exists ρa, In (A, ρa, B, ρb) tril).

(** Typing *)
Inductive term_type_check : listctx pty -> tm -> hty -> Prop :=
| TValue: forall Γ v ρ,
    Γ ⊢ v ⋮v ρ ->
    Γ ⊢ v ⋮t (pty_to_rty ρ)
| TSub: forall Γ e (τ1 τ2: hty),
    Γ ⊢WF τ2 ->
    Γ ⊢ e ⋮t τ1 -> Γ ⊢ τ1 ⪡ τ2 -> (Γ ⊢ e ⋮t τ2)
| TLetE: forall Γ e_x e Tx A T Bx_ρx BxB_ρ Bx_ρx_B_ρ (L: aset),
    Γ ⊢WF [: T | A ⇒ BxB_ρ ] ->
    Γ ⊢ e_x ⋮t [: Tx | A ⇒ Bx_ρx ] ->
    A_ρa_B_ρb_list_A_ρa Bx_ρx Bx_ρx_B_ρ ->
    A_ρa_B_ρb_list_AB_ρb BxB_ρ Bx_ρx_B_ρ ->
    (forall x, x ∉ L ->
          forall Bxi ρxi Bi ρi,
            In (Bxi, ρxi, Bi, ρi) Bx_ρx_B_ρ ->
            (Γ ++ [(x, ρxi)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A Bxi ⇒ [(Bi, ρi)]]) ->
    Γ ⊢ (tlete e_x e) ⋮t [: T | A ⇒ BxB_ρ ]
| TApp: forall Γ (v1 v2: value) e ρ Tx A T Bx_ρx BxB_ρ Bx_ρx_B_ρ (L: aset),
    Γ ⊢WF [: T | A ⇒ BxB_ρ ] ->
    Γ ⊢ v2 ⋮v ρ ->
    Γ ⊢ v1 ⋮v (-: ρ ⤑[: Tx | astar ∘ ⇒ Bx_ρx ]) ->
    A_ρa_B_ρb_list_A_ρa Bx_ρx Bx_ρx_B_ρ ->
    A_ρa_B_ρb_list_AB_ρb BxB_ρ Bx_ρx_B_ρ ->
    (forall x, x ∉ L ->
          forall Bxi ρxi Bi ρi,
            In (Bxi, ρxi, Bi, ρi) Bx_ρx_B_ρ ->
            (Γ ++ [(x, ρxi ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A (Bxi ^a^ v2) ⇒ [(Bi, ρi)]]) ->
    Γ ⊢ (tletapp v1 v2 e) ⋮t [: T | A ⇒ BxB_ρ ]
| TEffOp: forall Γ (op: effop) (v2: value) e ρ A Bx ϕx T opevent Bi ρi (L: aset),
    is_op_am op v2 ϕx opevent ->
    Γ ⊢WF [: T | A ⇒ [(aconcat opevent Bi, ρi)] ] ->
    builtin_typing_relation op (-: ρ ⤑[: ret_ty_of_op op | A ⇒ [(Bx, {v: ret_ty_of_op op | ϕx})] ]) ->
    Γ ⊢ v2 ⋮v ρ ->
    (forall x, x ∉ L ->
          (Γ ++ [(x, ({v: ret_ty_of_op op | ϕx}) ^p^ v2)]) ⊢ (e ^t^ x) ⋮t [: T | aconcat A opevent ⇒ [(Bi, ρi)]]) ->
    Γ ⊢ (tleteffop op v2 e) ⋮t [: T | A ⇒ [(aconcat opevent Bi, ρi)] ]
| TMatchb_true: forall Γ (v: value) e1 e2 τ,
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v (mk_eq_constant true) ->
    Γ ⊢ e1 ⋮t τ ->
    ⌊ Γ ⌋* ⊢t e2 ⋮t ⌊ τ ⌋ ->
    Γ ⊢ (tmatchb v e1 e2) ⋮t τ
| TMatchb_false: forall Γ (v: value) e1 e2 τ,
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v (mk_eq_constant false) ->
    Γ ⊢ e2 ⋮t τ ->
    ⌊ Γ ⌋* ⊢t e1 ⋮t ⌊ τ ⌋ ->
    Γ ⊢ (tmatchb v e1 e2) ⋮t τ
with value_type_check : listctx pty -> value -> pty -> Prop :=
| TContant: forall Γ (c: constant),
    Γ ⊢WFp (mk_eq_constant c) ->
    Γ ⊢ c ⋮v (mk_eq_constant c)
| TVar: forall Γ (x: atom) ρ,
    ctxfind Γ x = Some ρ ->
    Γ ⊢ x ⋮v ρ
| TLam: forall Γ b ρ e T A B (L: aset),
    Γ ⊢WFp (-: ρ ⤑[: T | A ⇒ B ] ) ->
    (forall x, x ∉ L -> (Γ ++ [(x, ρ)]) ⊢ (e ^t^ x) ⋮t ([: T | A ⇒ B ] ^h^ x)) ->
    Γ ⊢ (vlam b e) ⋮v (-: ρ ⤑[: T | A ⇒ B ])
| TLamFix: forall Γ b ρ e T A B (L: aset),
    Γ ⊢WFp (-: ρ ⤑[: T | A ⇒ B ]) ->
    (forall f, f ∉ L -> (Γ ++ [(f, (-: ρ ⤑[: T | A ⇒ B ]))]) ⊢ ((vlam b e) ^v^ f) ⋮v (-: ρ ⤑[: T | A ⇒ B ])) ->
    Γ ⊢ (vfix (⌊ -: ρ ⤑[: T | A ⇒ B ] ⌋) (vlam b e)) ⋮v (-: ρ ⤑[: T | A ⇒ B ])
where
"Γ '⊢' e '⋮t' τ" := (term_type_check Γ e τ) and "Γ '⊢' e '⋮v' τ" := (value_type_check Γ e τ).

Scheme value_type_check_rec := Induction for value_type_check Sort Prop
    with term_type_check_rec := Induction for term_type_check Sort Prop.

Lemma value_typing_regular: forall (Γ: listctx pty) (v: value) (ρ: pty),
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋.
Admitted.

Lemma tm_typing_regular: forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋.
Admitted.

Lemma well_formed_builtin_typing: forall op ρx A B ρ,
    builtin_typing_relation op (-: ρx ⤑[: ret_ty_of_op op | A ⇒ [(B, ρ)] ]) ->
    forall (v_x: constant), p⟦ ρx ⟧ v_x ->
                       forall α, a⟦ A ^a^ v_x ⟧ α ->
                            (exists (c: constant), p⟦ ρ ^p^ v_x ⟧ c) /\
                              (forall (c: constant), app{op, v_x}⇓{ α } c -> p⟦ ρ ^p^ v_x ⟧ c).
Admitted.

Lemma reduction_tlete:  forall e_x e α β v,
    α ⊧ tlete e_x e ↪*{ β } v <->
    (exists (βx βe: trace) (v_x: value),
      β = βx +;+ βe /\ α ⊧ e_x ↪*{ βx } v_x /\ α +;+ βx ⊧ (e ^t^ v_x) ↪*{ βe } v).
Admitted.

(* I have proved this lemma in Poirot. *)
Lemma msubst_open: forall (env: env) e (v_x: value) (x: atom),
    x # (dom env ∪ stale e ∪ stale v_x) ->
    tm_msubst env e ^t^ v_x = tm_msubst (<[x := v_x]> env) (e ^t^ x).
Admitted.

Lemma am_concat: forall A B α β,
  (a⟦A⟧) α ->
  (a⟦B⟧) β ->
  (a⟦ aconcat A B ⟧) (α +;+ β).
Admitted.

Theorem fundamental: forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ ->
    (* NOTE: [τ] being valid should be a regularity lemma. *)
    forall env, ctxRst Γ env -> ⟦ msubst hty_subst env τ ⟧ (tm_msubst env e).
Proof.
  apply (term_type_check_rec
           (* NOTE: should this be the denotation of [pty]? *)
           (fun Γ (v: value) ρ _ =>
              forall env,
                ctxRst Γ env ->
                ⟦ msubst hty_subst env (pty_to_rty ρ) ⟧ (value_msubst env v))
           (fun Γ e (τ: hty) _ =>
              forall env,
                ctxRst Γ env -> ⟦ msubst hty_subst env τ ⟧ (tm_msubst env e))
        ); intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - auto_pose_fv x. repeat specialize_with x.
    (* clear t t0. *)
    (* assert ((tm_msubst env (tlete e_x e)) = (tlete (tm_msubst env e_x) (tm_msubst env e))) as Hrewrite; auto. *)
    (* rewrite Hrewrite. clear Hrewrite. *)
    (* simpl. *)
    (* intros. *)
    (* rewrite reduction_tlete in H6. mydestr; subst. rewrite msubst_open with (x:=x) in H8. 2: { admit. } *)
    (* specialize (H env st H1 H2). simpl in H. *)
    (* assert (amlist_typed Bx_ρx Tx) as HH1. admit. *)
    (* rename x0 into βx. rename x2 into v_x. rename x1 into βe. *)
    (* specialize (H HH1 α βx v_x H5 H7). destruct H as (Bxi & ρxi & HinBx_ρx & Hβx & Hv_x). *)
    (* apply a in HinBx_ρx. destruct HinBx_ρx as (Bi & ρi & Hin). *)
    (* specialize (H0 _ _ _ _ Hin (<[ x := v_x]> env) st). (* Here st should be 1: st when v_x is a function 2: <[ x := v_x]> st when v_x is a constant *) *)
    (* assert (ctxRst (Γ ++ [(x, ρxi)]) (<[x:=v_x]> env)) as HH2. admit. *)
    (* assert (st⫕<[x:=v_x]> env) as HH3. admit. *)
    (* specialize (H0 HH2 HH3). simpl in H0. *)
    (* assert (amlist_typed [(Bi, ρi)] T) as HH4. admit. *)
    (* specialize (H0 HH4 (α +;+ βx) βe v). *)
    (* assert (closed_am 0 (dom st) (aconcat A Bxi)) as HH5. admit. *)
    (* assert ( *)
    (*     (closed_am 0 (dom st) (aconcat A Bxi)) /\ *)
    (*     (∃ α1 α2 : trace, α +;+ βx = α1 +;+ α2 ∧ ({0;b∅;st}a⟦A⟧) α1 ∧ ({0;b∅;st}a⟦Bxi⟧) α2)) as Hconcat. *)
    (* { split; eauto. } *)
    (* specialize (H0 Hconcat H8). clear Hconcat. *)
    (* destruct H0 as (Bi' & ρi' & Heq & Hβe & Hv). destruct Heq. 2: { inversion H. } inversion H; subst. *)
    (* rename Bi' into Bi. rename ρi' into ρi. *)
    (* exists (aconcat Bxi Bi), ρi. *)
    (* split. apply a0; eauto. split; auto. apply am_concat; auto. *)
Admitted.
