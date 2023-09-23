From stdpp Require Import mapset.
From CT Require Import Atom.
From CT Require Import Tactics.
From CT Require Import CoreLang.
From CT Require Import NamelessTactics.
Import CoreLang.
Import NamelessTactics.

(** * Most of lemmas in this file is inspired by Arthur Chargu´eraud's paper "The Locally Nameless Representation" : https://chargueraud.org/research/2009/ln/main.pdf *)
Lemma constant_eqb_spec: forall (c c': constant), c = c' \/ c <> c'.
Proof with eauto.
  destruct c, c'...
  - destruct b, b0; firstorder.
  - destruct (Nat.eq_dec n n0); firstorder.
    right. intro HH. inversion HH...
Qed.

Ltac specialize_L :=
  match goal with
  | [ H : forall (x: atom), x ∉ ?L -> _ |- _] => specialize (H (fv_of_set L) (fv_of_set_fresh L))
  end.

Lemma lc_exfalso: forall bn, ~ lc (vbvar bn).
Proof.
  intros bn HF. inversion HF.
Qed.

Lemma body_exfalso: forall bn, ~ body (vbvar (S bn)).
Proof.
  intros bn HF. inversion HF. specialize_L. inversion H.
Qed.

Ltac solve_lc_exfalso :=
  match goal with
    | [ H: lc (treturn (vbvar ?n)) |- _ ] => exfalso; apply (lc_exfalso n); auto
    | [ H: body (treturn (vbvar (S ?n))) |- _ ] => exfalso; apply (body_exfalso n); auto
  end.

Lemma lc_abs_iff_body: forall T e, lc (vlam T e) <-> body e.
Proof.
  split; unfold body; intros.
  - inversion H; subst. exists L. auto.
  - destruct H as (L & HL). eapply lc_vlam. apply HL.
Qed.

Ltac dec_tf := try (subst; rewrite decide_True; auto; fast_set_solver!!); try (rewrite decide_False; auto; fast_set_solver!!).

Lemma close_open_var_tm: forall (e: tm) (x: atom) (k: nat), x ∉ (fv_tm e) -> {k <t~ x} ({k ~t> x} e) = e.
Proof with eauto.
  apply (tm_mutual_rec
           (fun (v: value) => forall (x: atom) (k: nat), x ∉ (fv_value v) -> {k <v~ x} ({k ~v> x} v) = v)
           (fun (e: tm) => forall (x: atom) (k: nat), x ∉ (fv_tm e) -> {k <t~ x} ({k ~t> x} e) = e)
        ); simpl; try (intros; repeat rewrite_by_set_solver; auto).
  - assert (x <> atom) by fast_set_solver!!. apply decide_False...
  - destruct (Nat.eq_dec k bn).
    + rewrite decide_True... simpl... rewrite decide_True...
    + rewrite decide_False...
Qed.

Lemma close_open_var_value: forall (e: value) (x: atom) (k: nat), x ∉ (fv_value e) -> {k <v~ x} ({k ~v> x} e) = e.
Proof with eauto.
  apply (value_mutual_rec
           (fun (v: value) => forall (x: atom) (k: nat), x ∉ (fv_value v) -> {k <v~ x} ({k ~v> x} v) = v)
           (fun (e: tm) => forall (x: atom) (k: nat), x ∉ (fv_tm e) -> {k <t~ x} ({k ~t> x} e) = e)
        ); simpl; try (intros; repeat rewrite_by_set_solver; auto).
  - assert (x <> atom) by fast_set_solver!!. apply decide_False...
  - destruct (Nat.eq_dec k bn).
    + rewrite decide_True... simpl... rewrite decide_True...
    + rewrite decide_False...
Qed.

Lemma open_fv_value: forall (v: value) (u: value) (k: nat), fv_value ({k ~v> u} v) ⊆ fv_value u ∪ fv_value v.
Proof with eauto.
  apply (value_mutual_rec
           (fun (v: value) => forall (u: value) (k: nat), fv_value ({k ~v> u} v) ⊆ fv_value u ∪ fv_value v)
           (fun (e: tm) => forall (u: value) (k: nat), fv_tm ({k ~t> u} e) ⊆ fv_value u ∪ fv_tm e)
        ); simpl;
    try (intros; repeat rewrite_by_set_solver; auto);
    try var_dec_solver;
    try my_set_solver.
Qed.

Lemma open_fv_tm: forall (e: tm) (u: value) (k: nat), fv_tm ({k ~t> u} e) ⊆ fv_value u ∪ fv_tm e.
Proof with eauto.
  apply (tm_mutual_rec
           (fun (v: value) => forall (u: value) (k: nat), fv_value ({k ~v> u} v) ⊆ fv_value u ∪ fv_value v)
           (fun (e: tm) => forall (u: value) (k: nat), fv_tm ({k ~t> u} e) ⊆ fv_value u ∪ fv_tm e)
        ); simpl; intros; auto;
    try var_dec_solver;
    my_set_solver.
Qed.

Lemma open_fv_value': forall (v: value) (u: value) (k: nat), fv_value v ⊆ fv_value ({k ~v> u} v).
Proof with eauto.
  apply (value_mutual_rec
           (fun (v: value) => forall (u: value) (k: nat), fv_value v ⊆ fv_value ({k ~v> u} v))
           (fun (e: tm) => forall (u: value) (k: nat), fv_tm e ⊆ fv_tm ({k ~t> u} e))
        ); simpl;
    try my_set_solver.
Qed.

Lemma open_fv_tm': forall (e: tm) (x: value) (k: nat), fv_tm e ⊆ fv_tm ({k ~t> x} e).
Proof with eauto.
  apply (tm_mutual_rec
           (fun (v: value) => forall (u: value) (k: nat), fv_value v ⊆ fv_value ({k ~v> u} v))
           (fun (e: tm) => forall (u: value) (k: nat), fv_tm e ⊆ fv_tm ({k ~t> u} e))
        ); simpl;
    try my_set_solver.
Qed.

Lemma close_var_fv_value:
  forall (v: value) (x: atom) (k: nat), fv_value ({k <v~ x} v) = (fv_value v) ∖ {[x]}.
Proof.
  apply (value_mutual_rec
           (fun (v: value) => forall (x: atom) (k: nat), fv_value ({k <v~ x} v) = (fv_value v) ∖ {[x]})
           (fun (e: tm) => forall (x: atom) (k: nat), fv_tm ({k <t~ x} e) = (fv_tm e) ∖ {[x]})
        ); simpl; intros; auto;
    try var_dec_solver;
    my_set_solver.
Qed.

Lemma subst_fresh_value: forall (v: value) (x:atom) (u: value),
    x ∉ (fv_value v) -> {x := u}v v = v.
Proof with eauto.
  apply (value_mutual_rec
           (fun (v: value) => forall (x:atom) (u: value), x ∉ (fv_value v) -> {x := u}v v = v)
           (fun (e: tm) => forall (x:atom) (u: value), x ∉ (fv_tm e) -> {x := u}t e = e)
        ); simpl; intros; eauto; try (repeat rewrite_by_set_solver; auto).
  - assert (x <> atom) by my_set_solver. rewrite decide_False...
Qed.

Lemma subst_fresh_tm: forall (e: tm) (x:atom) (u: value),
    x ∉ (fv_tm e) -> {x := u}t e = e.
Proof with eauto.
  apply (tm_mutual_rec
           (fun (v: value) => forall (x:atom) (u: value), x ∉ (fv_value v) -> {x := u}v v = v)
           (fun (e: tm) => forall (x:atom) (u: value), x ∉ (fv_tm e) -> {x := u}t e = e)
        ); simpl; intros; eauto; try (repeat rewrite_by_set_solver; auto).
  - assert (x <> atom) by my_set_solver. rewrite decide_False...
Qed.

Ltac ex_specialize_L :=
  match goal with
  | [ H : ex (fun (L: aset) => _) |- _] => destruct H; specialize_L
  end.

(** There is a typo in the paper *)
Lemma fact1_tm: forall u v (e: tm) i j,
    i <> j -> {i ~t> u} ({j ~t> v} e) = {j ~t> v} e -> {i ~t> u} e = e.
Proof with auto.
  intros u v.
  apply (tm_mutual_rec
           (fun (e: value) => forall i j, i <> j -> {i ~v> u} ({j ~v> v} e) = {j ~v> v} e -> {i ~v> u} e = e)
           (fun (e: tm) => forall i j, i <> j -> {i ~t> u} ({j ~t> v} e) = {j ~t> v} e -> {i ~t> u} e = e)
        ); simpl; intros; auto;
    try repeat match goal with
               | [H: ?i <> ?j, H': context [_ -> _ = _], H'': ?a _ = ?a _ |- _ = _ ] =>
                   inversion H'';
                   (specialize (H' (S i) (S j)); rewrite H'; auto) || (specialize (H' i j); rewrite H'; auto)
               | [H: ?i <> ?j, H': context [_ -> _ = _], H'': ?a _ _ = ?a _ _ |- _ = _ ] =>
                   inversion H'';
                   (specialize (H' (S i) (S j)); rewrite H'; auto) || (specialize (H' i j); rewrite H'; auto)
               | [H: ?i <> ?j, H': context [_ -> _ = _], H'': ?a _ _ _ = ?a _ _ _ |- _ = _ ] =>
                   inversion H'';
                   (specialize (H' (S i) (S j)); rewrite H'; auto) || (specialize (H' i j); rewrite H'; auto)
               end.
  - repeat var_dec_solver.
Qed.

Lemma fact1_value: forall u v (e: value) i j,
    i <> j -> {i ~v> u} ({j ~v> v} e) = {j ~v> v} e -> {i ~v> u} e = e.
Proof with auto.
  intros u v.
  apply (value_mutual_rec
           (fun (e: value) => forall i j, i <> j -> {i ~v> u} ({j ~v> v} e) = {j ~v> v} e -> {i ~v> u} e = e)
           (fun (e: tm) => forall i j, i <> j -> {i ~t> u} ({j ~t> v} e) = {j ~t> v} e -> {i ~t> u} e = e)
        ); simpl; intros; auto;
    try repeat match goal with
               | [H: ?i <> ?j, H': context [_ -> _ = _], H'': ?a _ = ?a _ |- _ = _ ] =>
                   inversion H'';
                   (specialize (H' (S i) (S j)); rewrite H'; auto) || (specialize (H' i j); rewrite H'; auto)
               | [H: ?i <> ?j, H': context [_ -> _ = _], H'': ?a _ _ = ?a _ _ |- _ = _ ] =>
                   inversion H'';
                   (specialize (H' (S i) (S j)); rewrite H'; auto) || (specialize (H' i j); rewrite H'; auto)
               | [H: ?i <> ?j, H': context [_ -> _ = _], H'': ?a _ _ _ = ?a _ _ _ |- _ = _ ] =>
                   inversion H'';
                   (specialize (H' (S i) (S j)); rewrite H'; auto) || (specialize (H' i j); rewrite H'; auto)
               end.
  - repeat var_dec_solver.
Qed.

Lemma treturn_eq: forall (v1 v2: value), treturn v1 = treturn v2 -> v1 = v2.
Proof.
  intros. inversion H. auto.
Qed.

Lemma open_rec_lc_tm: forall (v: value) (u: tm) (k: nat), lc u -> {k ~t> v} u = u.
Proof with eauto.
  intros. generalize dependent k.
  induction H; simpl; intros; auto;
    try (repeat match goal with
                | [H: forall k, _ = _ |- _ ] => rewrite H; auto
                | [H: forall k, _ = _ |- _ ] =>
                    specialize (H k); simpl in H; apply treturn_eq in H; rewrite H
                end; auto;
         auto_eq_post;
         let accL := collect_stales tt in
         pose (Atom.fv_of_set accL) as y;
         pose (Atom.fv_of_set_fresh accL);
         repeat match goal with
                | [H: forall (x: atom), _ |- _ ] =>
                    specialize (H y)
                end;
         apply fact1_tm with (j := 0) (v:= vfvar y); auto; auto_apply; my_set_solver).
Qed.

Lemma open_rec_lc_value: forall (v: value) (u: value) (k: nat), lc u -> {k ~v> v} u = u.
Proof with eauto.
  intros.
  apply open_rec_lc_tm with (v:=v) (k:=k) in H. simpl in H. apply treturn_eq in H. auto.
Qed.

Lemma subst_open_value: forall (v: value) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}v ({k ~v> u} v) = ({k ~v> {x := w}v u} ({x := w}v v)).
Proof with eauto.
  apply (value_mutual_rec
           (fun (v: value) => forall (x:atom) (u: value) (w: value) (k: nat),
                lc w -> {x := w}v ({k ~v> u} v) = ({k ~v> {x := w}v u} ({x := w}v v)))
           (fun (e: tm) => forall (x:atom) (u: value) (w: value) (k: nat),
                lc w -> {x := w}t ({k ~t> u} e) = ({k ~t> {x := w}v u} ({x := w}t e)))
        ); simpl; intros; eauto; try (repeat rewrite_by_set_solver; auto);
    try repeat match goal with
               | [H: context [ tm_subst _ _ _ = _ ] |- _ ] => rewrite H; auto
               | [H: context [ value_subst _ _ _ = _ ] |- _ ] => rewrite H; auto
               end.
  - destruct (atom_dec x atom).
    + subst. rewrite decide_True... rewrite open_rec_lc_value; auto.
    + rewrite decide_False...
  - destruct (Nat.eq_dec k bn); simpl.
    + subst. rewrite decide_True... rewrite decide_True...
    + rewrite decide_False... rewrite decide_False...
Qed.

Lemma subst_open_tm: forall (v: tm) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}t ({k ~t> u} v) = ({k ~t> {x := w}v u} ({x := w}t v)).
Proof with eauto.
  apply (tm_mutual_rec
           (fun (v: value) => forall (x:atom) (u: value) (w: value) (k: nat),
                lc w -> {x := w}v ({k ~v> u} v) = ({k ~v> {x := w}v u} ({x := w}v v)))
           (fun (e: tm) => forall (x:atom) (u: value) (w: value) (k: nat),
                lc w -> {x := w}t ({k ~t> u} e) = ({k ~t> {x := w}v u} ({x := w}t e)))
        ); simpl; intros; eauto; try (repeat rewrite_by_set_solver; auto);
    try repeat match goal with
               | [H: context [ tm_subst _ _ _ = _ ] |- _ ] => rewrite H; auto
               | [H: context [ value_subst _ _ _ = _ ] |- _ ] => rewrite H; auto
               end.
  - destruct (atom_dec x atom).
    + subst. rewrite decide_True... rewrite open_rec_lc_value; auto.
    + rewrite decide_False...
  - destruct (Nat.eq_dec k bn); simpl.
    + subst. rewrite decide_True... rewrite decide_True...
    + rewrite decide_False... rewrite decide_False...
Qed.

Lemma close_var_rename_tm: forall x y (e: tm) k, y ∉ (fv_tm e) -> {k <t~ x} e = {k <t~ y} ({x := y}t e).
Proof with auto.
  intros x y.
  apply (tm_mutual_rec
           (fun (v: value) => forall k, y ∉ (fv_value v) -> {k <v~ x} v = {k <v~ y} ({x := y}v v))
           (fun (e: tm) => forall k, y ∉ (fv_tm e) -> {k <t~ x} e = {k <t~ y} ({x := y}t e))
        ); simpl; intros; auto; try (repeat rewrite_by_set_solver; auto).
  - destruct (atom_dec x atom).
     + subst. rewrite decide_True... rewrite decide_True... simpl. rewrite decide_True...
     + rewrite decide_False... rewrite decide_False... simpl.
       assert (y <> atom) by my_set_solver. rewrite decide_False...
Qed.

Lemma close_var_rename_value: forall x y (e: value) k, y ∉ (fv_value e) -> {k <v~ x} e = {k <v~ y} ({x := y}v e).
Proof with auto.
  intros x y.
  apply (value_mutual_rec
           (fun (v: value) => forall k, y ∉ (fv_value v) -> {k <v~ x} v = {k <v~ y} ({x := y}v v))
           (fun (e: tm) => forall k, y ∉ (fv_tm e) -> {k <t~ x} e = {k <t~ y} ({x := y}t e))
        ); simpl; intros; auto; try (repeat rewrite_by_set_solver; auto).
  - destruct (atom_dec x atom).
     + subst. rewrite decide_True... rewrite decide_True... simpl. rewrite decide_True...
     + rewrite decide_False... rewrite decide_False... simpl.
       assert (y <> atom) by my_set_solver. rewrite decide_False...
Qed.

(* The second class of lemmas *)

Lemma fact2_tm: forall (x y z: atom) (e: tm) i j,
    x <> y -> i <> j -> y ∉ fv_tm e ->
    {i ~t> y} ({j ~t> z} ({j <t~ x} e)) = {j ~t> z} ({j <t~ x} ({i ~t> y} e)).
Proof with auto.
  intros x y z.
  apply (tm_mutual_rec
           (fun (e: value) => forall i j,
                x <> y -> i <> j -> y ∉ fv_value e ->
                {i ~v> y} ({j ~v> z} ({j <v~ x} e)) = {j ~v> z} ({j <v~ x} ({i ~v> y} e)))
           (fun (e: tm) => forall i j,
                x <> y -> i <> j -> y ∉ fv_tm e ->
                {i ~t> y} ({j ~t> z} ({j <t~ x} e)) = {j ~t> z} ({j <t~ x} ({i ~t> y} e)))
        ); simpl; intros; auto; try (repeat rewrite_by_set_solver; auto); try (rewrite H; auto).
  - repeat var_dec_solver.
  - repeat var_dec_solver.
  - auto_eq_post; rewrite H0; auto; set_solver.
  - auto_eq_post; rewrite H0; auto; set_solver.
  - auto_eq_post; rewrite H1; auto; set_solver.
Qed.

Lemma fact2_value: forall (x y z: atom) (e: value) i j,
    x <> y -> i <> j -> y ∉ fv_tm e ->
    {i ~v> y} ({j ~v> z} ({j <v~ x} e)) = {j ~v> z} ({j <v~ x} ({i ~v> y} e)).
Proof with auto.
  intros x y z.
  apply (value_mutual_rec
           (fun (e: value) => forall i j,
                x <> y -> i <> j -> y ∉ fv_value e ->
                {i ~v> y} ({j ~v> z} ({j <v~ x} e)) = {j ~v> z} ({j <v~ x} ({i ~v> y} e)))
           (fun (e: tm) => forall i j,
                x <> y -> i <> j -> y ∉ fv_tm e ->
                {i ~t> y} ({j ~t> z} ({j <t~ x} e)) = {j ~t> z} ({j <t~ x} ({i ~t> y} e)))
        ); simpl; intros; auto; try (repeat rewrite_by_set_solver; auto); try (rewrite H; auto).
  - repeat var_dec_solver.
  - repeat var_dec_solver.
  - auto_eq_post; rewrite H0; auto; set_solver.
  - auto_eq_post; rewrite H0; auto; set_solver.
  - auto_eq_post; rewrite H1; auto; set_solver.
Qed.

Lemma subst_lc_tm: forall x (u: value) (t: tm), lc t -> lc u -> lc ({x := u}t t).
Proof with auto.
  intros x u t Hlct.
  induction Hlct; simpl; intros; auto; try (constructor; auto);
    try (auto_exists_L; intros; repeat split;
         repeat match goal with
                | [ H : context [lc _] |- lc (_ _ (vfvar ?x) _)] =>
                    specialize (H x);
                    rewrite subst_open_tm in H; auto; simpl in H;
                    rewrite decide_False in H; my_set_solver
                end).
  - repeat var_dec_solver.
Qed.

Lemma subst_lc_value: forall x (u: value) (t: value), lc t -> lc u -> lc ({x := u}t t).
Proof with auto.
  intros x u t Hlct.
  induction Hlct; simpl; intros; auto; try (constructor; auto);
    try (auto_exists_L; intros; repeat split;
         repeat match goal with
                | [ H : context [lc _] |- lc (_ _ (vfvar ?x) _)] =>
                    specialize (H x);
                    rewrite subst_open_tm in H; auto; simpl in H;
                    rewrite decide_False in H; my_set_solver
                end).
  - repeat var_dec_solver.
Qed.

Lemma open_close_var_tm_aux: forall (x: atom) (t: tm) (k: nat),
    {k ~t> x} t = t -> {k ~t> x} ({k <t~ x} t) = t.
Proof.
  intros x.
  apply (tm_mutual_rec
           (fun (t: value) => forall k, {k ~v> x} t = t -> {k ~v> x} ({k <v~ x} t) = t)
           (fun (t: tm) => forall k, {k ~t> x} t = t -> {k ~t> x} ({k <t~ x} t) = t));
    simpl; intros; auto;
    repeat (match goal with
         | [H: forall k, _ -> _ = _ |- _ ] => rewrite H; auto; clear H
         end); auto_eq_post; auto.
  - repeat var_dec_solver.
Qed.

Lemma open_close_var_tm: forall (x: atom) (t: tm), lc t -> {0 ~t> x} ({0 <t~ x} t) = t.
Proof.
  intros. apply open_close_var_tm_aux. apply open_rec_lc_tm; auto.
Qed.

Lemma open_close_var_value_aux: forall (x: atom) (t: value) (k: nat),
    {k ~v> x} t = t -> {k ~v> x} ({k <v~ x} t) = t.
Proof.
  intros x.
  apply (value_mutual_rec
           (fun (t: value) => forall k, {k ~v> x} t = t -> {k ~v> x} ({k <v~ x} t) = t)
           (fun (t: tm) => forall k, {k ~t> x} t = t -> {k ~t> x} ({k <t~ x} t) = t));
    simpl; intros; auto;
    repeat (match goal with
         | [H: forall k, _ -> _ = _ |- _ ] => rewrite H; auto; clear H
         end); auto_eq_post; auto.
  - repeat var_dec_solver.
Qed.

Lemma open_close_var_value: forall (x: atom) (t: value), lc t -> {0 ~v> x} ({0 <v~ x} t) = t.
Proof.
  intros. apply open_close_var_value_aux. apply open_rec_lc_value; auto.
Qed.

(* The third class of lemmas *)

Lemma subst_intro_tm: forall (v: tm) (x:atom) (w: value) (k: nat),
    x # v ->
    lc w -> {x := w}t ({k ~t> x} v) = ({k ~t> w} v).
Proof.
  intros.
  specialize (subst_open_tm v x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_tm; auto.
Qed.

Lemma subst_intro_value: forall (v: value) (x:atom) (w: value) (k: nat),
    x # v ->
    lc w -> {x := w}v ({k ~v> x} v) = ({k ~v> w} v).
Proof.
  intros.
  specialize (subst_open_value v x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_value; auto.
Qed.

Lemma subst_open_var_tm: forall x y (u: value) (t: tm) (k: nat),
    x <> y -> lc u -> {x := u}t ({k ~t> y} t) = ({k ~t> y} ({x := u}t t)).
Proof.
  intros.
  rewrite subst_open_tm; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_open_var_value: forall x y (u: value) (t: value) (k: nat),
    x <> y -> lc u -> {x := u}v ({k ~v> y} t) = ({k ~v> y} ({x := u}v t)).
Proof.
  intros.
  rewrite subst_open_value; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_body_tm: forall x (u: value) (t: tm), body t -> lc u -> body ({x := u}t t).
Proof with auto.
  intros.
  destruct H. auto_exists_L; intros; repeat split; auto.
  rewrite <- subst_open_var_tm; auto.
  apply subst_lc_tm; auto. apply H. my_set_solver. my_set_solver.
Qed.

Lemma subst_body_value: forall x (u: value) (t: value), body t -> lc u -> body ({x := u}v t).
Proof with auto.
  intros.
  destruct H. auto_exists_L; intros; repeat split; auto. simpl.
  rewrite <- subst_open_var_value; auto.
  apply subst_lc_value; auto. apply H. my_set_solver. my_set_solver.
Qed.

Lemma open_lc_tm: forall (u: value) (t: tm), body t -> lc u -> lc ({0 ~t> u} t).
Proof.
  intros. destruct H.
  let acc := collect_stales tt in pose acc.
  pose (Atom.fv_of_set a).
  assert (a0 ∉ a). apply Atom.fv_of_set_fresh.
  erewrite <- subst_intro_tm; auto. instantiate (1:= a0).
  apply subst_lc_tm; auto. apply H.
  my_set_solver. my_set_solver.
Qed.

Lemma open_lc_value: forall (u: value) (t: value), body t -> lc u -> lc ({0 ~v> u} t).
Proof.
  intros. destruct H.
  let acc := collect_stales tt in pose acc.
  pose (Atom.fv_of_set a).
  assert (a0 ∉ a). apply Atom.fv_of_set_fresh.
  erewrite <- subst_intro_value; auto. instantiate (1:= a0).
  apply subst_lc_value; auto. apply H.
  my_set_solver. my_set_solver.
Qed.

Lemma open_with_fresh_include_fv_tm: forall (x: atom) e k,
    x ∉ fv_tm e -> ({[x]} ∪ fv_tm e) ⊆ ({[x]} ∪ fv_tm ({k ~t> x} e)).
Proof.
  intros x.
  apply (tm_mutual_rec
           (fun (e: value) => forall k, x ∉ fv_tm e -> ({[x]} ∪ fv_value e) ⊆ ({[x]} ∪ fv_value ({k ~v> x} e)))
           (fun (e: tm) => forall k, x ∉ fv_tm e -> ({[x]} ∪ fv_tm e) ⊆ ({[x]} ∪ fv_tm ({k ~t> x} e)))
        ); simpl; intros; auto;
    try (var_dec_solver; fast_set_solver);
    repeat match goal with
           | [H: context [{_ ~v> _} ?e] |- context [{?k ~v> _} ?e]] => specialize (H k)
           | [H: context [{_ ~t> _} ?e] |- context [{?k ~t> _} ?e]] => specialize (H k)
           | [H: ?P -> _ ⊆ _ |- _] => assert P as Htmp by fast_set_solver; specialize (H Htmp); try clear Htmp
           end; repeat my_set_solver.
Qed.

Lemma open_with_fresh_include_fv_value: forall (x: atom) e k,
    x ∉ fv_value e -> ({[x]} ∪ fv_value e) ⊆ ({[x]} ∪ fv_value ({k ~v> x} e)).
Proof.
  intros x.
  apply (value_mutual_rec
           (fun (e: value) => forall k, x ∉ fv_tm e -> ({[x]} ∪ fv_value e) ⊆ ({[x]} ∪ fv_value ({k ~v> x} e)))
           (fun (e: tm) => forall k, x ∉ fv_tm e -> ({[x]} ∪ fv_tm e) ⊆ ({[x]} ∪ fv_tm ({k ~t> x} e)))
        ); simpl; intros; auto;
    try (var_dec_solver; fast_set_solver);
    repeat match goal with
           | [H: context [{_ ~v> _} ?e] |- context [{?k ~v> _} ?e]] => specialize (H k)
           | [H: context [{_ ~t> _} ?e] |- context [{?k ~t> _} ?e]] => specialize (H k)
           | [H: ?P -> _ ⊆ _ |- _] => assert P as Htmp by fast_set_solver; specialize (H Htmp); try clear Htmp
           end; repeat my_set_solver.
Qed.

(* Lemma for MNF *)

Ltac solve_let_lc_body H :=
  split; intros; try repeat split; auto;
    inversion H; subst; auto;
    try destruct_hyp_conj; try match goal with
    | [ H: body _ |- _ ] => inversion H; subst; clear H
    (* | [ H: lc _ |- _ ] => inversion H; subst; clear H *)
    end;
    auto_exists_L; intros; repeat split; auto;
    auto_apply; my_set_solver.

Lemma lete_lc_body: forall e1 e, lc (tlete e1 e) <-> lc e1 /\ body e.
Proof.
  solve_let_lc_body H.
Qed.

Lemma letapp_lc_body: forall (v1 v2: value) e, lc (tletapp v1 v2 e) <-> lc v1 /\ lc v2 /\ body e.
Proof.
  solve_let_lc_body H.
Qed.

Lemma leteffop_lc_body: forall op (v1: value) e, lc (tleteffop op v1 e) <-> lc v1 /\ body e.
Proof.
  solve_let_lc_body H.
Qed.

Lemma lc_fix_iff_body: forall T e, lc (vfix T e) <-> body e.
Proof.
  split; unfold body; intros.
  - inversion H; subst. exists L. auto.
  - destruct H as (L & HL). econstructor. apply HL.
Qed.

Lemma lc_implies_body_tm: forall (e: tm), lc e -> body e.
Proof. intros. exists ∅; intros; rewrite open_rec_lc_tm; auto.
Qed.

Lemma lc_implies_body_value: forall (e: value), lc e -> body e.
Proof. intros. exists ∅; intros. rewrite open_rec_lc_tm; auto.
Qed.

Ltac lc_solver :=
  repeat match goal with
    | [ |- lc (treturn (vfvar _))] => constructor
    | [ |- lc (tmatchb _ _ _)] => apply lc_tmatchb; (repeat split; auto)
    | [ |- lc (tletapp _ _ _)] => rewrite letapp_lc_body; (repeat split; auto)
    | [ |- lc (tleteffop _ _ _)] => rewrite leteffop_lc_body; (repeat split; auto)
    | [ |- lc (tlete _ _)] => rewrite lete_lc_body; split; auto
    | [ |- lc (treturn (vfix _ _))] => rewrite lc_fix_iff_body; auto
    | [ |- lc (treturn (vlam _ _))] => rewrite lc_abs_iff_body; auto
    | [H: lc (tlete _ ?e) |- body ?e ] => rewrite lete_lc_body in H; repeat destruct_hyp_conj; auto
    | [H: lc (tletapp _ _ ?e) |- body ?e ] => rewrite letapp_lc_body in H; repeat destruct_hyp_conj; auto
    | [H: lc (treturn (vlam _ ?e)) |- body ?e ] => rewrite lc_abs_iff_body in H; repeat destruct_hyp_conj; auto
    | [H: lc (treturn (vfix _ ?e)) |- body ?e ] => rewrite lc_fix_iff_body in H; repeat destruct_hyp_conj; auto
    | [H: lc (tletapp ?e _ _) |- lc (treturn ?e) ] => rewrite letapp_lc_body in H; repeat destruct_hyp_conj; auto
    | [H: lc (tletapp _ ?e _) |- lc (treturn ?e) ] => rewrite letapp_lc_body in H; repeat destruct_hyp_conj; auto
    | [H: lc ?e |- body ?e] => apply lc_implies_body_tm; auto
    | [H: lc ?e |- lc (?e ^t^ _)] => rewrite open_rec_lc_tm; auto
    | [|- body _ ] => eexists; auto_exists_L_intros
    end.

Lemma subst_as_close_open_tm_: forall (x: atom) (u: value) (e: tm) (k: nat),
    {k ~t> u} e = e ->
    {k ~t> u} ({k <t~ x} e) = {x := u}t e.
Proof.
  intros x u.
  apply (tm_mutual_rec
           (fun (e: value) => forall k, {k ~v> u} e = e -> {k ~v> u} ({k <v~ x} e) = {x := u}v e)
           (fun (e: tm) => forall k, {k ~t> u} e = e -> {k ~t> u} ({k <t~ x} e) = {x := u}t e)
        ); simpl; intros; eauto.
  - repeat var_dec_solver.
  (* - repeat var_dec_solver. invclear H0; auto. *)
  - rewrite H; auto. invclear H0. rewrite H2; auto.
  - rewrite H; auto. invclear H0. rewrite H2; auto.
  - rewrite H; auto. invclear H0. rewrite H2; auto.
  - rewrite H; auto. rewrite H0; auto.
    + invclear H1; rewrite H4; auto.
    + invclear H1; rewrite H3; auto.
  - rewrite H; auto. rewrite H0; auto.
    + invclear H1; rewrite H4; auto.
    + invclear H1; repeat rewrite H3; auto.
  - rewrite H; auto. rewrite H0; auto. rewrite H1; auto.
    + invclear H2; rewrite H6; auto.
    + invclear H2; repeat rewrite H5; auto.
    + invclear H2; repeat rewrite H4; auto.
  - rewrite H; auto. rewrite H0; auto. rewrite H1; auto.
    + invclear H2; rewrite H6; auto.
    + invclear H2; repeat rewrite H5; auto.
    + invclear H2; repeat rewrite H4; auto.
Qed.

Lemma subst_as_close_open_value_: forall (x: atom) (u: value) (e: value) (k: nat),
    {k ~v> u} e = e ->
    {k ~v> u} ({k <v~ x} e) = {x := u}v e.
Proof.
  intros x u.
  apply (value_mutual_rec
           (fun (e: value) => forall k, {k ~v> u} e = e -> {k ~v> u} ({k <v~ x} e) = {x := u}v e)
           (fun (e: tm) => forall k, {k ~t> u} e = e -> {k ~t> u} ({k <t~ x} e) = {x := u}t e)
        ); simpl; intros; eauto.
  - repeat var_dec_solver.
  (* - repeat var_dec_solver. invclear H0; auto. *)
  - rewrite H; auto. invclear H0. rewrite H2; auto.
  - rewrite H; auto. invclear H0. rewrite H2; auto.
  - rewrite H; auto. invclear H0. rewrite H2; auto.
  - rewrite H; auto. rewrite H0; auto.
    + invclear H1; rewrite H4; auto.
    + invclear H1; rewrite H3; auto.
  - rewrite H; auto. rewrite H0; auto.
    + invclear H1; rewrite H4; auto.
    + invclear H1; repeat rewrite H3; auto.
  - rewrite H; auto. rewrite H0; auto. rewrite H1; auto.
    + invclear H2; rewrite H6; auto.
    + invclear H2; repeat rewrite H5; auto.
    + invclear H2; repeat rewrite H4; auto.
  - rewrite H; auto. rewrite H0; auto. rewrite H1; auto.
    + invclear H2; rewrite H6; auto.
    + invclear H2; repeat rewrite H5; auto.
    + invclear H2; repeat rewrite H4; auto.
Qed.

Lemma subst_as_close_open_tm: forall (x: atom) (u: value) (e: tm),
    lc e -> {0 ~t> u} ({0 <t~ x} e) = {x := u}t e.
Proof.
  intros. eapply subst_as_close_open_tm_.
  rewrite open_rec_lc_tm; auto.
Qed.

Lemma subst_as_close_open_value: forall (x: atom) (u: value) (e: value),
    lc e -> {0 ~v> u} ({0 <v~ x} e) = {x := u}v e.
Proof.
  intros. eapply subst_as_close_open_value_.
  rewrite open_rec_lc_value; auto.
Qed.

Lemma close_fresh_rec_tm: forall (x: atom) (e: tm) (k: nat), x ∉ fv_tm e -> { k <t~ x} e = e.
Proof.
  intros x.
  apply (tm_mutual_rec
           (fun (v: value) => forall (k: nat), x ∉ fv_value v -> { k <v~ x} v = v)
           (fun (e: tm) => forall (k: nat), x ∉ fv_tm e -> { k <t~ x} e = e)
        ); simpl; intros; auto; try var_dec_solver; rewrite H; auto; try fast_set_solver;
    try (rewrite H0; auto; try fast_set_solver; rewrite H1; auto; try fast_set_solver).
Qed.

Lemma close_fresh_rec_value: forall (x: atom) (e: value) (k: nat), x ∉ fv_value e -> { k <v~ x} e = e.
Proof.
  intros x.
  apply (value_mutual_rec
           (fun (v: value) => forall (k: nat), x ∉ fv_value v -> { k <v~ x} v = v)
           (fun (e: tm) => forall (k: nat), x ∉ fv_tm e -> { k <t~ x} e = e)
        ); simpl; intros; auto; try var_dec_solver; rewrite H; auto; try fast_set_solver;
    try (rewrite H0; auto; try fast_set_solver; rewrite H1; auto; try fast_set_solver).
Qed.

Lemma subst_close_tm: ∀ (x y: atom) u, x ∉ fv_value u -> x <> y ->
                        forall e k, {k <t~ x} ({y := u }t e) = {y := u }t ({k <t~ x} e).
Proof.
  intros x y u Hux Hxy. apply (tm_mutual_rec
           (fun (e: value) => forall (k: nat), {k <v~ x} ({y := u }v e) = {y := u }v ({k <v~ x} e))
           (fun (e: tm) => forall (k: nat), {k <t~ x} ({y := u }t e) = {y := u }t ({k <t~ x} e))
        ); simpl; intros; auto;
    try (rewrite H; auto; rewrite H0; auto; rewrite H1; auto).
  repeat var_dec_solver; rewrite close_fresh_rec_value; auto.
Qed.

Lemma subst_close_value: ∀ (x y: atom) u, x ∉ fv_value u -> x <> y ->
                        forall e k, {k <v~ x} ({y := u }v e) = {y := u }v ({k <v~ x} e).
Proof.
  intros x y u Hux Hxy. apply (value_mutual_rec
           (fun (e: value) => forall (k: nat), {k <v~ x} ({y := u }v e) = {y := u }v ({k <v~ x} e))
           (fun (e: tm) => forall (k: nat), {k <t~ x} ({y := u }t e) = {y := u }t ({k <t~ x} e))
        ); simpl; intros; auto;
    try (rewrite H; auto; rewrite H0; auto; rewrite H1; auto).
  repeat var_dec_solver; rewrite close_fresh_rec_value; auto.
Qed.

Lemma subst_commute_tm: forall x u_x y u_y e,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }t ({y := u_y }t e) = {y := u_y }t ({x := u_x }t e).
Proof.
  intros x u_x y u_y e Hxy Hxuy Hyux. apply (tm_mutual_rec
           (fun (e: value) => {x := u_x }v ({y := u_y }v e) = {y := u_y }v ({x := u_x }v e))
           (fun (e: tm) => {x := u_x }t ({y := u_y }t e) = {y := u_y }t ({x := u_x }t e))
        ); simpl; intros; auto;
  try (rewrite H; auto; rewrite H0; auto; rewrite H1; auto);
  try (repeat var_dec_solver; rewrite subst_fresh_value; auto).
Qed.

Lemma subst_commute_value: forall x u_x y u_y e,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }v ({y := u_y }v e) = {y := u_y }v ({x := u_x }v e).
Proof.
  intros x u_x y u_y e Hxy Hxuy Hyux. apply (value_mutual_rec
           (fun (e: value) => {x := u_x }v ({y := u_y }v e) = {y := u_y }v ({x := u_x }v e))
           (fun (e: tm) => {x := u_x }t ({y := u_y }t e) = {y := u_y }t ({x := u_x }t e))
        ); simpl; intros; auto;
  try (rewrite H; auto; rewrite H0; auto; rewrite H1; auto);
  try (repeat var_dec_solver; rewrite subst_fresh_value; auto).
Qed.

Lemma subst_shadow_tm: forall (x z: atom) (u: value) (e: tm),
    x # e -> {x := u }t ({z := x }t e) = {z := u }t e.
Proof.
  intros x z u.
  apply (tm_mutual_rec
           (fun (e: value) => x # e -> {x := u }v ({z := x }v e) = {z := u }v e)
           (fun (e: tm) => x # e -> {x := u }t ({z := x }t e) = {z := u }t e)
        ); simpl; intros; eauto.
  - repeat var_dec_solver.
  - rewrite H; auto.
  - rewrite H; auto.
  - rewrite H; auto.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
    rewrite H1; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
    rewrite H1; auto; try fast_set_solver.
Qed.

Lemma subst_shadow_value: forall (x z: atom) (u: value) (e: value),
    x # e -> {x := u }v ({z := x }v e) = {z := u }v e.
Proof.
  intros x z u.
  apply (value_mutual_rec
           (fun (e: value) => x # e -> {x := u }v ({z := x }v e) = {z := u }v e)
           (fun (e: tm) => x # e -> {x := u }t ({z := x }t e) = {z := u }t e)
        ); simpl; intros; eauto.
  - repeat var_dec_solver.
  - rewrite H; auto.
  - rewrite H; auto.
  - rewrite H; auto.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
    rewrite H1; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
    rewrite H1; auto; try fast_set_solver.
Qed.

Lemma subst_subst_tm: ∀ (x : atom) (u_x : value) (y : atom) (u_y: value) (e: tm),
    x ≠ y → y ∉ fv_value u_x →
    {x := u_x }t ({y := u_y }t e) = {y := {x := u_x }v u_y }t ({x := u_x }t e).
Proof.
  intros x u_x y u_y e Hxy Hyux. apply (tm_mutual_rec
           (fun (e: value) => {x := u_x }v ({y := u_y }v e) = {y := {x := u_x }v u_y }v ({x := u_x }v e))
           (fun (e: tm) => {x := u_x }t ({y := u_y }t e) = {y := {x := u_x }v u_y }t ({x := u_x }t e))
        ); simpl; intros; auto;
  try (rewrite H; auto; rewrite H0; auto; rewrite H1; auto);
  try (repeat var_dec_solver; rewrite subst_fresh_value; auto).
Qed.

Lemma subst_subst_value: ∀ (x : atom) (u_x : value) (y : atom) (u_y e : value),
    x ≠ y → y ∉ fv_value u_x →
    {x := u_x }v ({y := u_y }v e) = {y := {x := u_x }v u_y }v ({x := u_x }v e).
Proof.
  intros x u_x y u_y e Hxy Hyux. apply (value_mutual_rec
           (fun (e: value) => {x := u_x }v ({y := u_y }v e) = {y := {x := u_x }v u_y }v ({x := u_x }v e))
           (fun (e: tm) => {x := u_x }t ({y := u_y }t e) = {y := {x := u_x }v u_y }t ({x := u_x }t e))
        ); simpl; intros; auto;
  try (rewrite H; auto; rewrite H0; auto; rewrite H1; auto);
  try (repeat var_dec_solver; rewrite subst_fresh_value; auto).
Qed.

Lemma fv_of_subst_value: forall x (u e: value), fv_value ({x := u }v e) ⊆ (fv_value e ∖ {[x]}) ∪ fv_value u.
Proof.
  intros x u. apply (value_mutual_rec
           (fun (e: value) => fv_value ({x := u }v e) ⊆ fv_value e ∖ {[x]} ∪ fv_value u)
           (fun (e: tm) => fv_tm ({x := u }t e) ⊆ fv_tm e ∖ {[x]} ∪ fv_value u)
        ); simpl; intros; auto; repeat var_dec_solver; set_solver.
Qed.

Lemma fv_of_subst_tm: forall x (u : value) (e: tm), fv_tm ({x := u }t e) ⊆ (fv_tm e ∖ {[x]}) ∪ fv_value u.
Proof.
  intros x u. apply (tm_mutual_rec
           (fun (e: value) => fv_value ({x := u }v e) ⊆ fv_value e ∖ {[x]} ∪ fv_value u)
           (fun (e: tm) => fv_tm ({x := u }t e) ⊆ fv_tm e ∖ {[x]} ∪ fv_value u)
        ); simpl; intros; auto; repeat var_dec_solver; set_solver.
Qed.

Lemma fv_of_subst_value_closed: forall x (u e: value),
    fv_value u ≡ ∅ ->
    fv_value ({x := u }v e) = (fv_value e ∖ {[x]}).
Proof.
  intros x u.
  apply (value_mutual_rec
           (fun (e: value) =>
              fv_value u ≡ ∅ -> fv_value ({x := u }v e) = fv_value e ∖ {[x]})
           (fun (e: tm) =>
              fv_value u ≡ ∅ -> fv_tm ({x := u }t e) = fv_tm e ∖ {[x]})
        ); simpl; intros; auto; repeat var_dec_solver; set_solver.
Qed.

Lemma fv_of_subst_tm_closed: forall x (u: value) e,
    fv_value u ≡ ∅ -> fv_tm ({x := u }t e) = (fv_tm e ∖ {[x]}).
Proof.
  intros x u.
  apply (tm_mutual_rec
           (fun (e: value) =>
              fv_value u ≡ ∅ -> fv_value ({x := u }v e) = fv_value e ∖ {[x]})
           (fun (e: tm) =>
              fv_value u ≡ ∅ -> fv_tm ({x := u }t e) = fv_tm e ∖ {[x]})
        ); simpl; intros; auto; repeat var_dec_solver; set_solver.
Qed.

Lemma body_vbvar_0: body (vbvar 0).
Proof.
  unfold body. exists ∅. intros. constructor.
Qed.

Global Hint Resolve body_vbvar_0: core.

Lemma lc_tletapp: forall (v x: value), lc v -> lc x -> lc (tletapp v x (vbvar 0)).
Proof.
  intros. auto_exists_L; simpl; intros; auto.
Qed.

Global Hint Resolve lc_tletapp: core.

Lemma body_tletapp_0: forall (v: value), lc v -> body (tletapp v (vbvar 0) (vbvar 0)).
Proof.
  intros. auto_exists_L; intros. simpl.
  rewrite open_rec_lc_value; auto.
Qed.

Global Hint Resolve body_tletapp_0: core.

Lemma open_subst_same_tm: forall x y e k, x # e -> {x := y }t ({k ~t> x} e) = {k ~t> y} e.
Proof.
  intros x y. apply (tm_mutual_rec
                   (fun (e: value) => forall k,
                      x # e -> {x := y }v ({k ~v> x} e) = {k ~v> y} e)
                   (fun (e: tm) => forall k,
                      x # e -> {x := y }t ({k ~t> x} e) = {k ~t> y} e)
                ); simpl; intros; auto.
  - repeat var_dec_solver.
  - repeat var_dec_solver.
  - rewrite H; auto.
  - rewrite H; auto.
  - rewrite H; auto.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
    rewrite H1; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
    rewrite H1; auto; try fast_set_solver.
Qed.

Lemma open_subst_same_value: forall x y e k, x # e -> {x := y }v ({k ~v> x} e) = {k ~v> y} e.
Proof.
  intros x y. apply (value_mutual_rec
                   (fun (e: value) => forall k,
                      x # e -> {x := y }v ({k ~v> x} e) = {k ~v> y} e)
                   (fun (e: tm) => forall k,
                      x # e -> {x := y }t ({k ~t> x} e) = {k ~t> y} e)
                ); simpl; intros; auto.
  - repeat var_dec_solver.
  - repeat var_dec_solver.
  - rewrite H; auto.
  - rewrite H; auto.
  - rewrite H; auto.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
    rewrite H1; auto; try fast_set_solver.
  - rewrite H; auto; try fast_set_solver. rewrite H0; auto; try fast_set_solver.
    rewrite H1; auto; try fast_set_solver.
Qed.

Lemma body_vlam_eq: forall e T1 T2,
    body (vlam T1 e) <-> body (vlam T2 e).
Proof.
  apply (tm_mutual_rec
                   (fun (e: value) => forall T1 T2, body (vlam T1 e) <-> body (vlam T2 e))
                   (fun (e: tm) => forall T1 T2, body (vlam T1 e) <-> body (vlam T2 e))
                ); split; simpl; intros; auto;
    repeat match goal with
    | [H: body (treturn (vlam _ _)) |- _ ] => invclear H
    | [|- body (treturn (vlam _ _))] => auto_exists_L; intros a; intros; specialize_with a
    | [H: context [(treturn (vlam _ _)) ^t^ _] |- _ ] => simpl in H
    | [|- context [(treturn (vlam _ _)) ^t^ _] ] => simpl
    | [H: lc (treturn (vlam _ _)) |- _ ] => rewrite lc_abs_iff_body in H; auto
    | [|- lc (treturn (vlam _ _))] => rewrite lc_abs_iff_body; auto
    end.
Qed.

Lemma close_rm_fv_tm: forall x e k, x ∉ fv_tm ({k <t~ x} e).
Proof.
  intros x e.
  apply (tm_mutual_rec
           (fun (e: value) => forall k, x ∉ fv_value ({k <v~ x} e))
           (fun (e: tm) => forall k, x ∉ fv_tm ({k <t~ x} e))
        ); simpl; intros; auto; repeat var_dec_solver; set_solver.
Qed.

Lemma close_rm_fv_value: forall x e k, x ∉ fv_value ({k <v~ x} e).
Proof.
  intros x e.
  apply (value_mutual_rec
           (fun (e: value) => forall k, x ∉ fv_value ({k <v~ x} e))
           (fun (e: tm) => forall k, x ∉ fv_tm ({k <t~ x} e))
        ); simpl; intros; auto; repeat var_dec_solver; set_solver.
Qed.

Lemma close_then_subst_same_tm: forall x v_x e,
  ({x := v_x }t (x \t\ e)) = (x \t\ e).
Proof.
  intros. rewrite subst_fresh_tm; auto. apply close_rm_fv_tm.
Qed.

Lemma close_then_subst_same_value: forall x v_x e,
  ({x := v_x }v (x \v\ e)) = (x \v\ e).
Proof.
  intros. rewrite subst_fresh_value; auto. apply close_rm_fv_value.
Qed.

Lemma subst_open_tm_closed:
  ∀ (v : tm) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }t ({k ~t> u} v) = {k ~t> u} ({x := w }t v).
Proof.
  intros. rewrite subst_open_tm; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_open_value_closed:
  ∀ (v : value) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }v ({k ~v> u} v) = {k ~v> u} ({x := w }v v).
Proof.
  intros. rewrite subst_open_value; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma body_lc_after_close_tm: forall (x: atom) e, lc e -> body ({0 <t~ x} e).
Proof.
  intros. unfold body. auto_exists_L. intros.
  rewrite subst_as_close_open_tm; auto.
  apply subst_lc_tm; auto.
Qed.

Lemma body_lc_after_close_value: forall (x: atom) (e: value), lc e -> body ({0 <v~ x} e).
Proof.
  intros. unfold body. auto_exists_L. intros. simpl.
  rewrite subst_as_close_open_value; auto.
  apply subst_lc_value; auto.
Qed.

Lemma lc_fresh_var_implies_body: forall e (x: atom),
  x # e -> lc (e ^t^ x) -> body e.
Proof.
  intros.
  apply (body_lc_after_close_tm x) in H0. rewrite close_open_var_tm in H0; auto.
Qed.

Lemma open_not_in_eq_tm (x : atom) (t : tm) k :
  x # {k ~t> x} t ->
  forall e, t = {k ~t> e} t
with open_not_in_eq_value (x : atom) (v : value) k :
  x # {k ~v> x} v ->
  forall e, v = {k ~v> e} v.
Proof.
  all : specialize (open_not_in_eq_tm x).
  all : specialize (open_not_in_eq_value x).
  all : destruct t || destruct v; simpl; intros; repeat f_equal.
  all: try solve [ auto_apply; eauto; my_set_solver ].
  case_decide; subst. my_set_solver. eauto.
Qed.

Lemma lc_subst_tm: forall x (u: value) (t: tm), lc ({x := u}t t) -> lc u -> lc t.
Proof.
  intros.
  remember ({x:=u}t t).
  revert dependent t.
  induction H; intros;
    repeat
      match goal with
      | H : _ = {_:=_}t ?t |- _ => destruct t; simpl in *; simplify_eq
      | H : _ = {_:=_}v ?v |- _ => destruct v; simpl in *; simplify_eq
      end; eauto using lc.

  all:
  econstructor; eauto;
  let x := fresh "x" in
  let acc := collect_stales tt in instantiate (1 := acc); intros x **; simpl;
  repeat specialize_with x;
  rewrite <- subst_open_var_tm in * by (eauto; my_set_solver);
  eauto.
Qed.

Lemma lc_subst_value: forall x (u: value) (v: value), lc ({x := u}v v) -> lc u -> lc v.
Proof.
  intros.
  sinvert H;
    repeat
      match goal with
      | H : _ = {_:=_}t ?t |- _ => destruct t; simpl in *; simplify_eq
      | H : _ = {_:=_}v ?v |- _ => destruct v; simpl in *; simplify_eq
      end; eauto using lc.
  all:
  econstructor; eauto;
  let x := fresh "x" in
  let acc := collect_stales tt in instantiate (1 := acc); intros x **; simpl;
  repeat specialize_with x;
  rewrite <- subst_open_var_tm in * by (eauto; my_set_solver);
  eauto using lc_subst_tm.
Qed.

Lemma open_swap_tm: forall (t: tm) i j (u v: value),
    lc u ->
    lc v ->
    i <> j ->
    {i ~t> v} ({j ~t> u} t) = {j ~t> u} ({i ~t> v} t)
with open_swap_value: forall (t: value) i j (u v: value),
    lc u ->
    lc v ->
    i <> j ->
    {i ~v> v} ({j ~v> u} t) = {j ~v> u} ({i ~v> v} t).
Proof.
  all: intros; destruct t; simpl; try reflexivity.
  6 : {
    repeat (case_decide; simpl; subst); try easy;
    rewrite !open_rec_lc_value; eauto.
  }
  all: f_equal; eauto.
Qed.

Lemma open_lc_respect_tm: forall (t: tm) (u v : value) k,
    lc ({k ~t> u} t) ->
    lc u ->
    lc v ->
    lc ({k ~t> v} t).
Proof.
  intros * H. remember ({k ~t> u} t) as t'.
  revert dependent t. revert k.
  induction H; intros;
    repeat
      match goal with
      | H : _ = {_ ~t> _} ?t |- _ =>
          destruct t; simpl in *; simplify_eq
      | H : _ = {_ ~v> _} ?v |- _ =>
          destruct v; simpl in *; try case_decide; simplify_eq
      end; eauto.
  all:
  econstructor;
  change (lc ({?k ~v> ?u} ?v)) with (lc ({k ~t> u} v)); eauto;
  let x := fresh "x" in
  let acc := collect_stales tt in instantiate (1 := acc); intros x **; simpl;
  repeat specialize_with x;
  rewrite open_swap_tm in * by eauto; eauto.
Qed.

Lemma open_lc_respect_value: forall (t: value) (u v : value) k,
    lc ({k ~v> u} t) ->
    lc u ->
    lc v ->
    lc ({k ~v> v} t).
Proof.
  intros * H. remember (treturn ({k ~v> u} t)) as t'.
  revert dependent t. revert k.
  induction H; intros;
    repeat
      match goal with
      | H : _ = treturn ({_ ~v> _} ?v) |- _ =>
          destruct v; simpl in *; try case_decide; simplify_eq
      end; eauto.
  all:
  econstructor;
  let x := fresh "x" in
  let acc := collect_stales tt in instantiate (1 := acc); intros x **; simpl;
  repeat specialize_with x;
  rewrite open_swap_tm in * by eauto; eauto using open_lc_respect_tm.
Qed.


Global Hint Resolve lc_fresh_var_implies_body: core.
