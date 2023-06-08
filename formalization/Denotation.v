From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Coq.Program Require Import Wf.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementType.
From CT Require Import Instantiation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import BasicTyping.
Import RefinementType.
Import Substitution.
Import Qualifier.
Import Equation.
Import mapset.

Inductive repeat_tr: (trace -> Prop) -> trace -> Prop :=
| repeat_tr0: forall p, repeat_tr p ϵ
| repeat_tr1: forall (p: trace -> Prop) α β, p α -> repeat_tr p β -> repeat_tr p (α +;+ β).

(** Regular language *)

Definition bpropR (ϕ: qualifier) (c: constant) : Prop :=
  denote_qualifier (ϕ ^q^ c).

Definition bpropR2 (ϕ: qualifier) (c1: constant) (c2: constant) : Prop :=
  denote_qualifier (ϕ ^q^ c1 ^q^ c2).

Fixpoint langA (a: am) (α: trace) {struct a} : Prop :=
  closed_am ∅ a /\
    match a with
    | aemp => False
    | aϵ => α = ϵ
    | aevent op ϕ =>
        exists (c1 c: constant),
          α = tr{op, c1, c} /\ ∅ ⊢t c1 ⋮v TNat /\ ∅ ⊢t c ⋮v (ret_ty_of_op op) /\
          bpropR2 ϕ c1 c
    | aconcat a1 a2 =>
        exists α1 α2, α = α1 +;+ α2 ∧ langA a1 α1 /\ langA a2 α2
    | aunion a1 a2 => langA a1 α ∨ langA a2 α
    | astar a => repeat_tr (langA a) α
    | acomp a => ~ langA a α /\ ~ with_retv α
    end.

Notation "'a⟦' a '⟧' " :=
  (langA a) (at level 20, format "a⟦ a ⟧", a constr).

(** Type Denotation: *)

(* Fixpoint ty_size (t: ty) := *)
(*   match t with *)
(*   | t1 ⤍ t2 => S (ty_size t1 + ty_size t2) *)
(*   | _ => 0 *)
(*   end. *)

Fixpoint ptyR (t: ty) (ρ: pty) (e: tm) : Prop :=
  ⌊ ρ ⌋ = t /\ ∅ ⊢t e ⋮t ⌊ ρ ⌋ /\ closed_pty ∅ ρ /\
    match ρ with
    | {v: b | ϕ } =>
        (* NOTE: why we type [c] here? *)
        forall (c: constant), e ↪* c -> ∅ ⊢t c ⋮v b /\ bpropR ϕ c
    | -: {v:b | ϕ} ⤑[: T | A ⇒ B ] =>
        match t with
        | TBase _ => False
        | TArrow t1 t2 =>
            amlist_typed B T ->
            forall (v_x: constant),
              ptyR t1 {v:b | ϕ} v_x ->
              forall (α β: trace) (v: value),
                a⟦ A ^a^ v_x ⟧ α ->
                α ⊧ (mk_app_e_v e v_x) ↪*{ β } v ->
                exists Bi ρi, In (Bi, ρi) B /\
                           a⟦ Bi ^a^ v_x ⟧ β /\
                           ptyR t2 (ρi ^p^ v_x) v
        end
    | -: (-: ρ ⤑[: Tx | ax ⇒ bx ]) ⤑[: T | A ⇒ B ] =>
        match t with
        | TBase _ => False
        | TArrow t1 t2 =>
            amlist_typed B T ->
            forall (v_x: value),
              ptyR t1 (-: ρ ⤑[: Tx | ax ⇒ bx ]) v_x ->
              forall (α β: trace) (v: value),
                a⟦ A ⟧ α ->
                α ⊧ (mk_app_e_v e v_x) ↪*{ β } v ->
                exists Bi ρi, In (Bi, ρi) B /\
                           a⟦ Bi ⟧ β /\
                           ptyR t2 ρi v
        end
    end.

Notation "'p⟦' ρ '⟧' " :=
  (ptyR ⌊ ρ ⌋  ρ) (at level 20, format "p⟦ ρ ⟧", ρ constr).

Definition htyR τ (e: tm) : Prop :=
  match τ with
  | [: T | A ⇒ B ] =>
      amlist_typed B T ->
      forall (α β: trace) (v: value),
        a⟦ A ⟧ α ->
        α ⊧ e ↪*{ β } v ->
        exists Bi ρi, In (Bi, ρi) B /\
                   a⟦ Bi ⟧ β /\
                   p⟦ ρi ⟧ v
  end.

Notation "'⟦' τ '⟧' " :=
  (htyR τ) (at level 20, format "⟦ τ ⟧", τ constr).

(* TODO: make this a computation? *)
Definition substitution_included_by_env (st: amap constant) (env: env) : Prop :=
  forall (x: atom), st !! x = None <-> env !! x = None /\ (forall (c: constant), st !! x = Some c <-> env !! x = Some (vconst c)).

Notation " st '⫕' env " :=
  (substitution_included_by_env st env) (at level 20, format "st ⫕ env").

Inductive ctxRst: listctx pty -> env -> Prop :=
| ctxRst0: ctxRst [] ∅
| ctxRst1: forall Γ env (x: atom) ρ (v: value),
    ctxRst Γ env ->
    (* [ok_ctx] implies [ρ] is closed and valid, meaning that it does not use
    any function variables. *)
    ok_ctx (Γ ++ [(x, ρ)]) ->
    p⟦ msubst pty_subst env ρ ⟧ v ->
    ctxRst (Γ ++ [(x, ρ)]) (<[ x := v ]> env).
