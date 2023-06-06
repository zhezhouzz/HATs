From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Coq.Program Require Import Wf.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementType.

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

Definition bpropR (bst: bsubstitution) (st: substitution) (ϕ: qualifier) (c: constant) : Prop :=
  match ϕ with
  | (bp[ _ | _ | p ]) => p (<b[↦ c ]> bst) st
  end.

Fixpoint langA (n: nat) (bst: bsubstitution) (st: substitution) (a: am) (α: trace) {struct a} : Prop :=
  closed_am n (dom st) a /\
    match a with
    | aemp => False
    | aϵ => α = ϵ
    | aevent op ϕ => ∃ (c: constant), α = trevent op c /\ ∅ ⊢t c ⋮v TNat /\ bpropR bst st ϕ c
| aconcat a1 a2 => exists α1 α2, α = α1 +;+ α2 ∧ langA n bst st a1 α1 /\ langA n bst st a2 α2
| aunion a1 a2 => langA n bst st a1 α ∨ langA n bst st a2 α
| astar a => repeat_tr (langA n bst st a) α
| acomp a => ~ langA n bst st a α /\ ~ with_retv α
end.

Notation " '{' n ';' bst ';' st '}a⟦' ρ '⟧' " :=
  (langA n bst st ρ) (at level 20, format "{ n ; bst ; st }a⟦ ρ ⟧", bst constr, st constr, ρ constr).
Notation " '{' st '}a⟦' ρ '⟧' " := (fun e => langA 0 b∅ st ρ e) (at level 20, format "{ st }a⟦ ρ ⟧", st constr, ρ constr).

(** Type Denotation: *)

(* Fixpoint ty_size (t: ty) := *)
(*   match t with *)
(*   | t1 ⤍ t2 => S (ty_size t1 + ty_size t2) *)
(*   | _ => 0 *)
(*   end. *)

Fixpoint ptyR (n: nat) (bst: bsubstitution) (st: substitution) (t: ty) (ρ: pty) (e: tm) : Prop :=
  ⌊ ρ ⌋ = t /\ ∅ ⊢t e ⋮t ⌊ ρ ⌋ /\ closed_pty n (dom st) ρ /\
    match ρ with
    | {v: b | ϕ } => forall (c: constant), e ↪* c -> ∅ ⊢t c ⋮v b /\ bpropR bst st ϕ c
    | -: {v:b | ϕ} ⤑[: T | A ⇒ B ] =>
        match t with
        | TBase _ => False
        | TArrow t1 t2 =>
            amlist_typed B T ->
            forall (v_x: constant), ptyR n bst st t1 {v:b | ϕ} v_x ->
                               forall (α β: trace) (v: value),
                                 { n ; <b[↦ v_x ]> bst ; st }a⟦ A ⟧ α ->
                                 α ⊧ (mk_app_e_v e v_x) ↪*{ β } v ->
                                 exists Bi ρi, In (Bi, ρi) B /\
                                            { n ; <b[↦ v_x ]> bst ; st }a⟦ Bi ⟧ β /\
                                            ptyR n (<b[↦ v_x ]> bst) st t2 ρi v
        end
    | -: (-: ρ ⤑[: Tx | ax ⇒ bx ]) ⤑[: T | A ⇒ B ] =>
         match t with
         | TBase _ => False
         | TArrow t1 t2 =>
             amlist_typed B T ->
             forall (v_x: value), ptyR n bst st t1 (-: ρ ⤑[: Tx | ax ⇒ bx ]) v_x ->
                             forall (α β: trace) (v: value),
                               { n ; bst ; st }a⟦ A ⟧ α ->
                               α ⊧ (mk_app_e_v e v_x) ↪*{ β } v ->
                               exists Bi ρi, In (Bi, ρi) B /\
                                          { n ; bst ; st }a⟦ Bi ⟧ β /\
                                          ptyR n bst st t2 ρi v end
    end.

Notation " '{' n ';' bst ';' st '}p⟦' ρ '⟧' " :=
  (ptyR n bst st ⌊ ρ ⌋  ρ) (at level 20, format "{ n ; bst ; st }p⟦ ρ ⟧", bst constr, st constr, ρ constr).
Notation " '{' st '}p⟦' ρ '⟧' " := (fun e => ptyR 0 b∅ st ⌊ ρ ⌋ ρ e) (at level 20, format "{ st }p⟦ ρ ⟧", st constr, ρ constr).

Definition htyR (n: nat) (bst: bsubstitution) (st: substitution) τ (e: tm) : Prop :=
  match τ with
  | [: T | A ⇒ B ] =>
      amlist_typed B T ->
      forall (α β: trace) (v: value),
        { n ; bst ; st }a⟦ A ⟧ α ->
        α ⊧ e ↪*{ β } v ->
        exists Bi ρi, In (Bi, ρi) B /\
                   { n ; bst ; st }a⟦ Bi ⟧ β /\
                   { n ; bst ; st }p⟦ ρi ⟧ v
  end.

Notation " '{' n ';' bst ';' st '}⟦' ρ '⟧' " :=
  (htyR n bst st ρ) (at level 20, format "{ n ; bst ; st }⟦ ρ ⟧", bst constr, st constr, ρ constr).
Notation " '{' st '}⟦' ρ '⟧' " := (fun e => htyR 0 b∅ st ρ e) (at level 20, format "{ st }⟦ ρ ⟧", st constr, ρ constr).

Definition substitution_included_by_env (st: amap constant) (env: amap value) : Prop :=
  forall (x: atom), st !! x = None <-> env !! x = None /\ (forall (c: constant), st !! x = Some c <-> env !! x = Some (vconst c)).

Notation " st '⫕' env " :=
  (substitution_included_by_env st env) (at level 20, format "st ⫕ env").

Inductive ctxRst: listctx pty -> amap value -> Prop :=
| ctxRst0: ctxRst [] ∅
| ctxRst1: forall Γ (st: substitution) env (x: atom) ρ (v: value),
    ctxRst Γ env ->
    ok_ctx (Γ ++ [(x, ρ)]) ->
    (forall st, st ⫕ env -> { st }p⟦ ρ ⟧ v) ->
    ctxRst (Γ ++ [(x, ρ)]) (<[ x := v ]> env).
