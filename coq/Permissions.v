Require Import HahnBase.
Require Import List.
Require Import ListSet.
Require Import Permutation.
Require Import PermutationTactic.
Require Import Prerequisites.
Require Import QArith.
Require Import Qcanon.
Require Import Utf8.

Import ListNotations.

Open Scope Qc_scope.


(** * Permissions *)

Lemma Q2Qc_correct :
  forall q : Q, Q2Qc q == q.
Proof.
  intros. apply Qred_correct.
Qed.

Lemma Qcplus_lt_compat :
  forall x y z t : Qc,
  x < y -> z < t -> x + z < y + t.
Proof.
  ins. unfold Qcplus, Qclt.
  repeat rewrite Q2Qc_correct.
  apply Qplus_lt_le_compat. easy.
  now apply Qlt_le_weak.
Qed.

Lemma Qcplus_le_mono_l :
  forall x y z : Qc, x <= y <-> z + x <= z + y.
Proof.
  split; intros.
  - apply Qcplus_le_compat. apply Qcle_refl. exact H.
  - replace x with ((0 - z) + (z + x)) by ring.
    replace y with ((0 - z) + (z + y)) by ring.
    apply Qcplus_le_compat; intuition. apply Qcle_refl.
Qed.

Lemma Qcplus_le_mono_r :
  forall x y z : Qc, x <= y <-> x + z <= y + z.
Proof.
  ins. intuition.
  rewrite Qcplus_comm with x z.
  rewrite Qcplus_comm with y z.
  by apply Qcplus_le_mono_l.
  apply Qcplus_le_mono_l with z.
  rewrite Qcplus_comm with z x.
  by rewrite Qcplus_comm with z y.
Qed.

Lemma Qclt_nge :
  forall x y : Qc, x < y <-> ~ y <= x.
Proof.
  split; auto using Qclt_not_le, Qcnot_le_lt.
Qed.

Lemma Qclt_irrefl :
  forall q : Qc, ~ q < q.
Proof.
  ins. apply Qcle_not_lt, Qcle_refl.
Qed.

Lemma Qclt_asymm :
  forall q1 q2 : Qc,
  q1 < q2 -> ~ q2 < q1.
Proof.
  intros q1 q2 H1 H2.
  assert (q1 < q1). { by apply Qclt_trans with q2. }
  by apply Qclt_irrefl with q1.
Qed.

Lemma Qcplus_lt_mono_l :
  forall x y z : Qc, x < y <-> z + x < z + y.
Proof.
  ins. rewrite !Qclt_nge.
  by rewrite <- Qcplus_le_mono_l.
Qed.

Lemma Qcplus_lt_mono_r :
  forall x y z : Qc, x < y <-> x + z < y + z.
Proof.
  ins. rewrite !Qclt_nge.
  by rewrite <- Qcplus_le_mono_r.
Qed.

Lemma Qcplus_lt_compat_le_l :
  forall x y z t : Qc,
  x <= y -> z < t -> x + z < y + t.
Proof.
  intros x y z t H1 H2.
  apply Qcle_lt_or_eq in H1.
  destruct H1 as [H1 | H1].
  - by apply Qcplus_lt_compat.
  - clarify. by apply Qcplus_lt_mono_l.
Qed.

Lemma Qcplus_lt_compat_le_r :
  forall x y z t : Qc,
  x < y -> z <= t -> x + z < y + t.
Proof.
  intros x y z t H1 H2.
  apply Qcle_lt_or_eq in H2.
  destruct H2 as [H2 | H2].
  - by apply Qcplus_lt_compat.
  - clarify. by apply Qcplus_lt_mono_r.
Qed.

Lemma Qcplus_pos_nonneg :
  forall p q : Qc, 0 < p -> 0 <= q -> 0 < p + q.
Proof.
  intros p q Hp Hq.
  apply Qclt_le_trans with (p + 0).
  by rewrite Qcplus_0_r.
  by apply Qcplus_le_mono_l.
Qed.

Lemma Qcplus_swap_l :
  forall q1 q2 q3 : Qc, q1 + (q2 + q3) = q2 + (q1 + q3).
Proof.
  intros q1 q2 q3.
  rewrite Qcplus_comm, <- Qcplus_assoc.
  by rewrite Qcplus_comm with q1 q3.
Qed.

Lemma Qcplus_swap_r :
  forall q1 q2 q3 : Qc, q1 + (q2 + q3) = q3 + (q2 + q1).
Proof.
  ins. rewrite Qcplus_comm.
  rewrite <- Qcplus_assoc.
  apply Qcplus_swap_l.
Qed.

Lemma Qcplus_pos_le_elim :
  forall q1 q2 q : Qc, q1 + q2 <= q -> 0 <= q2 -> q1 <= q.
Proof.
  intros q1 q2 q H1 H2.
  replace q1 with (q1 + 0).
  apply Qcle_trans with (q1 + q2); auto.
  by rewrite <- Qcplus_le_mono_l.
  apply Qcplus_0_r.
Qed.

Lemma Qcplus_pos_lt_elim :
  forall q1 q2 q : Qc, q1 + q2 < q -> 0 <= q2 -> q1 < q.
Proof.
  intros q1 q2 q H1 H2.
  replace q1 with (q1 + 0).
  apply Qcle_lt_trans with (q1 + q2); auto.
  by rewrite <- Qcplus_le_mono_l.
  apply Qcplus_0_r.
Qed.

Lemma Qcplus_le_weaken :
  forall q1 q2 q : Qc, 0 < q -> q1 <= q2 -> q1 <= q2 + q.
Proof.
  intros q1 q2 q H1 H2.
  rewrite Qcplus_comm.
  replace q1 with (0 + q1).
  apply Qcplus_le_compat; auto.
  by apply Qclt_le_weak in H1.
  apply Qcplus_0_l.
Qed.

Lemma Qcplus_lt_weaken :
  forall q1 q2 q : Qc,
  0 < q -> q1 <= q2 -> q1 < q2 + q.
Proof.
  intros q1 q2 q H1 H2.
  apply Qcle_lt_or_eq in H2.
  destruct H2 as [H2 | H2].
  (* [q1] is less than [q2] *)
  - rewrite Qcplus_comm.
    replace q1 with (0 + q1).
    apply Qcplus_lt_compat; auto.
    apply Qcplus_0_l.
  (* [q1] is equal to [q2] *)
  - clarify.
    apply Qclt_minus_iff.
    rewrite <- Qcplus_assoc.
    rewrite Qcplus_comm.
    rewrite <- Qcplus_assoc.
    rewrite Qcplus_comm with (- q2) q2.
    by rewrite Qcplus_opp_r, Qcplus_0_r.
Qed.

Lemma Qcle_diff :
  forall q1 q2 : Qc, q1 <= q2 -> exists q, q2 = q1 + q.
Proof.
  intros q1 q2 H.
  apply Qcle_minus_iff in H.
  exists (q2 + (- q1)).
  rewrite Qcplus_comm.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_comm with (-q1) q1.
  rewrite Qcplus_opp_r.
  by rewrite Qcplus_0_r.
Qed.

Lemma Qclt_diff :
  forall q1 q2 : Qc, q1 < q2 -> exists q, q2 = q + q1.
Proof.
  intros q1 q2 H.
  apply Qclt_minus_iff in H.
  exists (q2 + (- q1)).
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_comm with (-q1) q1.
  rewrite Qcplus_opp_r.
  by rewrite Qcplus_0_r.
Qed.

Lemma Qclt_mono_pos :
  forall q1 q2 : Qc, 0 < q1 -> q2 < q2 + q1.
Proof.
  intros q1 q2 H.
  replace (q2 < q2 + q1) with (q2 + 0 < q2 + q1).
  by apply Qcplus_lt_mono_l.
  by rewrite Qcplus_0_r.
Qed.

Lemma Qcle_plus_elim :
  forall q1 q2 q3 : Qc, 0 <= q1 -> 0 <= q2 -> q1 + q2 <= q3 -> q1 <= q3.
Proof.
  intros q1 q2 q3 H1 H2 H3.
  apply Qcle_trans with (q1 + q2); auto.
  replace (q1 <= q1 + q2) with (q1 + 0 <= q1 + q2).
  by apply Qcplus_le_mono_l.
  by rewrite Qcplus_0_r.
Qed.

Lemma Qcle_weaken :
  forall q1 q2 : Qc, q1 = q2 -> q1 <= q2.
Proof.
  intros ?? H. rewrite H.
  apply Qcle_refl.
Qed.

Lemma Qcplus_canc_l :
  forall q1 q2 q : Qc, q + q1 = q + q2 -> q1 = q2.
Proof.
  intros q1 q2 q H.
  apply Qcle_antisym.
  apply Qcplus_le_mono_l with q.
  by apply Qcle_weaken.
  apply Qcplus_le_mono_l with q.
  by apply Qcle_weaken.
Qed.

Lemma Qcplus_canc_r :
  forall q1 q2 q : Qc, q1 + q = q2 + q -> q1 = q2.
Proof.
  intros q1 q2 q H.
  apply Qcplus_canc_l with q.
  rewrite Qcplus_comm with q q1.
  by rewrite Qcplus_comm with q q2.
Qed.

Lemma Qcplus_neg_dist :
  forall q1 q2 : Qc, -(q1 + q2) = (-q1) + (-q2).
Proof.
  intros q1 q2.
  apply Qcplus_canc_r with (q1 + q2).
  rewrite Qcplus_comm.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_comm with q1 q2.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_comm.
  repeat rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  rewrite <- Qcplus_comm.
  rewrite Qcplus_opp_r.
  reflexivity.
Qed.

Lemma Qcplus_pos_le :
  forall q1 q2 : Qc, 0 < q2 -> q1 <= q1 + q2.
Proof.
  intros q1 q2 H.
  rewrite <- Qcplus_0_r with q1.
  rewrite <- Qcplus_assoc.
  rewrite <- Qcplus_le_mono_l.
  rewrite Qcplus_0_l.
  by apply Qclt_le_weak.
Qed.


(** ** Fractional permissions *)

(** Fractional permissions are rational numbers in the range (0..1]. The rational
    number [1] is defined to be _full_. Moreover, [0] is an (example of an) _invalid_
    fractional permission (although there are many rational numbers that are not
    fractional permissions). *)

Definition perm_full := 1%Qc.


(** *** Validity *)

(** The predicate [perm_valid] is used to determine whether a rational number is a
    fractional permission (i.e. is within the proper range). *)

Definition perm_valid (q : Qc) : Prop :=
  0 < q /\ q <= 1.

Notation "√ q" := (perm_valid q) (only printing, at level 80).

Lemma perm_valid_mono :
  forall q1 q2 : Qc,
  perm_valid q1 -> q2 < q1 + q2.
Proof.
  intros q1 q2 H.
  unfold perm_valid in H. intuition.
  replace q2 with (0 + q2) at 1.
  by rewrite <- Qcplus_lt_mono_r.
  by rewrite Qcplus_0_l.
Qed.

Lemma perm_valid_pos :
  forall q : Qc, perm_valid q -> 0 < q.
Proof.
  unfold perm_valid. ins. desf.
Qed.

Hint Resolve perm_valid_pos.

Lemma perm_valid_full_neg :
  forall q : Qc,
  perm_valid q -> ~ perm_full < q.
Proof.
  intros q H1 H2.
  unfold perm_valid in H1.
  destruct H1 as (H1 & H3).
  unfold perm_full in H2.
  apply Qcle_lt_or_eq in H3.
  destruct H3 as [H3 | H3]; vauto.
  by apply Qclt_asymm in H2.
Qed.

Lemma perm_valid_full :
  forall q : Qc,
  perm_valid q ->
  perm_full <= q ->
  q = perm_full.
Proof.
  intros q H1 H2.
  apply Qcle_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; auto.
  by apply perm_valid_full_neg in H2.
Qed.


(** *** Disjointness *)

(** Two permissions are _disjoint_ if they are both positive and their sum does not exceed 1. *)

Definition perm_disj (q1 q2 : Qc) : Prop :=
  0 < q1 /\ 0 < q2 /\ q1 + q2 <= 1.

Notation "q1 ⟂ q2" := (perm_disj q1 q2) (only printing, at level 80).

Instance perm_disj_symm :
  Symmetric perm_disj.
Proof.
  unfold perm_disj. red. intuition.
  by rewrite Qcplus_comm.
Qed.

Hint Resolve perm_disj_symm.

Lemma perm_disj_valid_l :
  forall q1 q2 : Qc, perm_disj q1 q2 -> perm_valid q1.
Proof.
  unfold perm_disj, perm_valid. intuition.
  apply Qcplus_pos_le_elim in H2. auto.
  by apply Qclt_le_weak in H.
Qed.

Lemma perm_disj_valid_r :
  forall q1 q2 : Qc, perm_disj q1 q2 -> perm_valid q2.
Proof.
  intros ?? H. symmetry in H.
  by apply perm_disj_valid_l in H.
Qed.

Lemma perm_disj_valid :
  forall q1 q2 : Qc, perm_disj q1 q2 -> perm_valid q1 /\ perm_valid q2.
Proof.
  intros ?? H. split.
  by apply perm_disj_valid_l in H.
  by apply perm_disj_valid_r in H.
Qed.

Lemma perm_disj_add_l :
  forall q1 q2 q3 : Qc,
  perm_disj q1 q2 -> perm_disj (q1 + q2) q3 -> perm_disj q2 q3.
Proof.
  unfold perm_disj.
  intros q1 q2 q3. intuition.
  apply Qcplus_pos_le_elim with (q2 := q1).
  by rewrite <- Qcplus_comm, Qcplus_assoc.
  by apply Qclt_le_weak.
Qed.

Lemma perm_disj_add_r :
  forall q1 q2 q3 : Qc,
  perm_disj q2 q3 -> perm_disj q1 (q2 + q3) -> perm_disj q1 q2.
Proof.
  unfold perm_disj.
  intros q1 q2 q3. intuition.
  apply Qcplus_pos_le_elim with (q2 := q3).
  by rewrite <- Qcplus_assoc.
  now apply Qclt_le_weak.
Qed.

Lemma perm_disj_assoc_l :
  forall q1 q2 q3 : Qc,
  perm_disj q1 q2 -> perm_disj (q1 + q2) q3 -> perm_disj q1 (q2 + q3).
Proof.
  unfold perm_disj. intuition.
  apply Qcplus_pos_nonneg; auto.
  by apply Qclt_le_weak.
  by rewrite Qcplus_assoc.
Qed.

Lemma perm_disj_assoc_r :
  forall q1 q2 q3 : Qc,
  perm_disj q2 q3 -> perm_disj q1 (q2 + q3) -> perm_disj (q1 + q2) q3.
Proof.
  unfold perm_disj. intuition.
  apply Qcplus_pos_nonneg; auto.
  by apply Qclt_le_weak.
  by rewrite <- Qcplus_assoc.
Qed.

Lemma perm_add_valid :
  forall q1 q2 : Qc, perm_disj q1 q2 -> perm_valid (q1 + q2).
Proof.
  unfold perm_disj, perm_valid.
  intros ?? H. intuition.
  apply Qcplus_pos_nonneg. auto.
  by apply Qclt_le_weak in H.
Qed.

Lemma perm_lt_weaken :
  forall q q1 q2 : Qc,
  perm_disj q1 q2 -> q < q1 -> q < q1 + q2.
Proof.
  intros q q1 q2 H1 H2.
  unfold perm_disj in H1. desf.
  apply Qcplus_lt_weaken; auto.
  by apply Qclt_le_weak.
Qed.

Lemma perm_le_weaken :
  forall q q1 q2 : Qc,
  perm_disj q1 q2 -> q <= q1 -> q <= q1 + q2.
Proof.
  intros q q1 q2 H1 H2.
  unfold perm_disj in H1. desf.
  by apply Qcplus_le_weaken.
Qed.

Lemma perm_disj_full_neg_l :
  forall q : Qc, ~ perm_disj q perm_full.
Proof.
  intros q H.
  unfold perm_disj in H.
  intuition desf.
  assert (perm_full < q + perm_full).
  unfold perm_full in *.
  rewrite Qcplus_comm.
  by apply Qclt_mono_pos.
  unfold perm_full in *.
  by apply Qclt_not_le in H1.
Qed.

Lemma perm_disj_full_neg_r :
  forall q : Qc, ~ perm_disj perm_full q.
Proof.
  intros q H. symmetry in H.
  by apply perm_disj_full_neg_l in H.
Qed.

Lemma perm_lt_diff :
  forall q1 q2 : Qc,
  perm_valid q1 ->
  perm_valid q2 ->
  q1 < q2 ->
  exists q3, perm_disj q1 q3 /\ q1 + q3 = q2.
Proof.
  intros q1 q2 H1 H2 H3.
  apply Qclt_minus_iff in H3.
  exists (q2 + (- q1)). split; auto.
  (* left part of conjunction *)
  - red. intuition auto.
    rewrite Qcplus_comm.
    rewrite <- Qcplus_assoc.
    rewrite Qcplus_comm with (-q1) q1.
    rewrite Qcplus_opp_r.
    rewrite Qcplus_0_r.
    unfold perm_valid in H2. desf.
  (* right part of conjunction *)
  - rewrite Qcplus_comm.
    rewrite <- Qcplus_assoc.
    rewrite Qcplus_comm with (-q1) q1.
    rewrite Qcplus_opp_r.
    by rewrite Qcplus_0_r.
Qed.

Lemma perm_disj_lt :
  forall q1 q2 q3,
  perm_valid q1 ->
  perm_disj q2 q3 ->
  q1 < q2 ->
  perm_disj q1 q3.
Proof.
  intros q1 q2 q3 H1 H2 H3.
  unfold perm_valid in H1.
  destruct H1 as (H1 & H4).
  unfold perm_disj in *.
  destruct H2 as (H2 & H5 & H6).
  intuition.
  apply Qcle_trans with (q2 + q3); auto.
  apply Qcplus_le_mono_r.
  by apply Qclt_le_weak.
Qed.

Lemma perm_disj_le :
  forall q1 q2 q3,
  perm_valid q1 ->
  perm_disj q2 q3 ->
  q1 <= q2 ->
  perm_disj q1 q3.
Proof.
  intros q1 q2 q3 H1 H2 H3.
  apply Qcle_lt_or_eq in H3.
  destruct H3 as [H3 | H3]; vauto.
  by apply perm_disj_lt with q2.
Qed.


(** ** Permission sequences *)

(** This section defines operations on _sequences_ of fractional permissions. *)

(** *** Validity *)

(** A sequence of fractional permissions is _valid_ if all permissions are valid individually. *)

Fixpoint perm_valid_list (xs : list Qc) : Prop :=
  match xs with
    | nil => True
    | q :: xs' => perm_valid q /\ perm_valid_list xs'
  end.

Notation "√ qs" := (perm_valid_list qs) (only printing, at level 80).

Lemma perm_valid_list_single :
  forall q, perm_valid_list [q] <-> perm_valid q.
Proof.
  intuition simpls. desf.
Qed.

Hint Resolve perm_valid_list_single.

Lemma perm_valid_list_permutation :
  forall xs1 xs2,
  Permutation xs1 xs2 -> perm_valid_list xs1 -> perm_valid_list xs2.
Proof.
  intros ?? H ?. induction H; simpls; desf; intuition.
Qed.

Add Parametric Morphism : perm_valid_list
  with signature @Permutation Qc ==> iff
    as perm_valid_list_permut_mor.
Proof.
  intros xs ys ?. intuition.
  apply perm_valid_list_permutation with xs; auto.
  apply perm_valid_list_permutation with ys; auto.
Qed.


(** *** Positivity *)

(** A sequence of fractional permissions is _positive_ if
    all rationals in the list are positive. *)

Fixpoint perm_pos_list (xs : list Qc) : Prop :=
  match xs with
    | nil => True
    | q :: xs' => 0 < q /\ perm_pos_list xs'
  end.

Lemma perm_pos_list_In :
  forall qs q, perm_pos_list qs -> In q qs -> 0 < q.
Proof.
  induction qs; ins.
  desf. by apply IHqs.
Qed.

Lemma perm_pos_list_permutation :
  forall xs ys,
  Permutation xs ys -> perm_pos_list xs -> perm_pos_list ys.
Proof.
  intros xs ys H1 H2.
  induction H1; simpls; intuition.
Qed.

Add Parametric Morphism : perm_pos_list
  with signature @Permutation Qc ==> iff
    as perm_pos_list_permut_mor.
Proof.
  intros xs ys ?. intuition.
  apply perm_pos_list_permutation with xs; auto.
  apply perm_pos_list_permutation with ys; auto.
Qed.

Ltac perm_pos_list_solve :=
  match goal with
    | [ _ : (perm_pos_list ?X) |- (perm_pos_list _) ] =>
      apply perm_pos_list_permutation with X; auto; list_permutation;
        fail "perm_pos_list_solve can not solve this system."
    | [ |- _ ] => fail "perm_pos_list_solve can not be applied."
  end.

Lemma perm_pos_list_add_left :
  forall q1 q2 qs,
  perm_pos_list (q1 :: q2 :: qs) -> perm_pos_list (q1 + q2 :: qs).
Proof.
  simpls. intuition.
  apply Qcplus_pos_nonneg; auto.
  by apply Qclt_le_weak.
Qed.

Lemma perm_pos_list_add :
  forall qs1 q1 q2 qs2,
  perm_pos_list (qs1 ++ q1 :: q2 :: qs2) ->
  perm_pos_list (qs1 ++ q1 + q2 :: qs2).
Proof.
  induction qs1; simpls; intuition.
  apply Qcplus_pos_nonneg; auto.
  by apply Qclt_le_weak.
Qed.

Lemma perm_pos_list_tail :
  forall q qs,
  perm_pos_list (q :: qs) -> perm_pos_list qs.
Proof.
  ins. desf.
Qed.

Lemma perm_pos_list_sub_l :
  forall xs ys,
  perm_pos_list (xs ++ ys) -> perm_pos_list xs.
Proof.
  induction xs; intros ys H; simpls.
  intuition. by apply IHxs with ys.
Qed.

Lemma perm_pos_list_sub_r :
  forall xs ys,
  perm_pos_list (xs ++ ys) -> perm_pos_list ys.
Proof.
  intros xs ys H.
  rewrite Permutation_app_comm in H.
  by apply perm_pos_list_sub_l in H.
Qed.

Lemma perm_pos_list_remove :
  forall q xs ys,
  perm_pos_list (xs ++ q :: ys) -> perm_pos_list (xs ++ ys).
Proof.
  intros ??? H.
  rewrite <- Permutation_middle in H.
  by apply perm_pos_list_tail in H.
Qed.

Lemma perm_pos_list_remove_list :
  forall xs ys zs,
  perm_pos_list (xs ++ ys ++ zs) -> perm_pos_list (xs ++ zs).
Proof.
  intros xs ys zs H.
  rewrite perm_takeit_1 in H.
  by apply perm_pos_list_sub_r in H.
Qed.

Lemma perm_valid_list_pos :
  forall qs, perm_valid_list qs -> perm_pos_list qs.
Proof.
  induction qs; intro H; simpls.
  unfold perm_valid in *. intuition.
Qed.

Hint Resolve perm_valid_list_pos.

Lemma perm_pos_list_cons :
  forall q qs,
  0 < q -> perm_pos_list qs -> perm_pos_list (q :: qs).
Proof.
  ins.
Qed.

Lemma perm_pos_list_app :
  forall xs ys,
  perm_pos_list xs -> perm_pos_list ys -> perm_pos_list (xs ++ ys).
Proof.
  induction xs; intros ys H1 H2; simpls.
  intuition.
Qed.

Lemma perm_pos_list_assoc_l :
  forall q1 q2 q3 qs,
  perm_pos_list [q2; q3] ->
  perm_pos_list (q1 :: q2 + q3 :: qs) ->
  perm_pos_list (q1 + q2 :: q3 :: qs).
Proof.
  ins. intuition.
  apply Qcplus_pos_nonneg; auto.
  by apply Qclt_le_weak.
Qed.

Lemma perm_pos_list_assoc_r :
  forall q1 q2 q3 qs,
  perm_pos_list [q1; q2] ->
  perm_pos_list (q1 + q2 :: q3 :: qs) ->
  perm_pos_list (q1 :: q2 + q3 :: qs).
Proof.
  ins. intuition.
  apply Qcplus_pos_nonneg; auto.
  by apply Qclt_le_weak.
Qed.

Lemma perm_pos_list_set_remove :
  forall xs x,
  perm_pos_list xs -> perm_pos_list (set_remove Qc_eq_dec x xs).
Proof.
  induction xs; ins; simpls; desf; intuition vauto.
  apply perm_pos_list_cons. auto.
  by apply IHxs.
Qed.

Lemma perm_pos_list_sublist :
  forall xs ys,
  sublist Qc_eq_dec xs ys -> perm_pos_list ys -> perm_pos_list xs.
Proof.
  induction xs; ins; simpls; desf; intuition vauto.
  by apply perm_pos_list_In in H.
  apply IHxs in H1; vauto.
  by apply perm_pos_list_set_remove.
Qed.


(** *** Addition *)

(** The _addition_ of a sequence of fractional permissions is defined as classical summation. *)

Fixpoint perm_add_list (xs : list Qc) : Qc :=
  match xs with
    | nil => 0
    | q :: xs' => q + perm_add_list xs'
  end.

Notation "∑ xs" := (perm_add_list xs) (only printing, at level 80).

Lemma perm_add_list_permutation :
  forall xs ys,
  Permutation xs ys -> perm_add_list xs = perm_add_list ys.
Proof.
  intros xs ys H. induction H; simpls.
  by rewrite IHPermutation.
  by rewrite Qcplus_swap_l.
  by rewrite IHPermutation1, IHPermutation2.
Qed.

Add Parametric Morphism : perm_add_list
  with signature @Permutation Qc ==> eq
    as perm_add_list_permut_mor.
Proof.
  ins. by apply perm_add_list_permutation.
Qed.

Lemma perm_add_list_single :
  forall q, perm_add_list [q] = q.
Proof.
  ins. apply Qcplus_0_r.
Qed.

Hint Rewrite perm_add_list_single.

Lemma perm_add_list_nonneg :
  forall qs, perm_pos_list qs -> 0 <= perm_add_list qs.
Proof.
  intros qs H. induction qs; simpls; desf.
  replace 0 with (0 + 0); auto.
  apply Qcplus_le_compat.
  by apply Qclt_le_weak.
  by apply IHqs.
Qed.

Lemma perm_add_list_add_left :
  forall q1 q2 qs,
  perm_add_list (q1 :: q2 :: qs) = perm_add_list (q1 + q2 :: qs).
Proof.
  intros q1 q2 qs. simpls.
  apply Qcplus_assoc.
Qed.

Lemma perm_add_list_add :
  forall qs1 q1 q2 qs2,
  perm_add_list (qs1 ++ q1 :: q2 :: qs2) = perm_add_list (qs1 ++ q1 + q2 :: qs2).
Proof.
  induction qs1; intuition simpls.
  apply Qcplus_assoc.
  by rewrite IHqs1.
Qed.

Lemma perm_add_list_left :
  forall x xs,
  perm_add_list (x :: xs) = x + perm_add_list xs.
Proof.
  simpls.
Qed.

Lemma perm_add_list_set_remove :
  forall qs q,
  set_In q qs ->
  perm_add_list (set_remove Qc_eq_dec q qs) = perm_add_list qs + - q.
Proof.
  induction qs; ins; simpls; desf; intuition vauto.
  rewrite Qcplus_comm, Qcplus_assoc.
  rewrite Qcplus_comm with (- q) q.
  by rewrite Qcplus_opp_r, Qcplus_0_l.
  rewrite Qcplus_comm, Qcplus_assoc.
  rewrite Qcplus_comm with (- a) a.
  by rewrite Qcplus_opp_r, Qcplus_0_l.
  rewrite perm_add_list_left.
  rewrite IHqs; auto.
  by rewrite <- Qcplus_assoc.
Qed.

Lemma perm_add_list_sublist :
  forall xs ys,
  sublist Qc_eq_dec xs ys ->
  perm_pos_list ys ->
  perm_add_list xs <= perm_add_list ys.
Proof.
  induction xs; ins; simpls; desf; intuition vauto.
  by apply perm_add_list_nonneg in H0.
  apply IHxs in H1.
  rewrite perm_add_list_set_remove in H1; auto.
  rewrite Qcplus_le_mono_r with (z := - a).
  rewrite Qcplus_comm, Qcplus_assoc.
  rewrite Qcplus_comm with (- a) a.
  by rewrite Qcplus_opp_r, Qcplus_0_l.
  by apply perm_pos_list_set_remove.
Qed.


(** *** Disjointness *)

(** A sequence of fractional permissions is _disjoint_ if all the rationals are positive and
    the sum of all rationals in the list does not exceed one. *)

Definition perm_disj_list (qs : list Qc) : Prop :=
  perm_pos_list qs /\ perm_add_list qs <= 1.

Notation "⫡ xs" := (perm_disj_list xs) (only printing, at level 80).

Lemma perm_disj_list_permutation :
  forall xs ys,
  Permutation xs ys -> perm_disj_list xs -> perm_disj_list ys.
Proof.
  unfold perm_disj_list.
  intuition by rewrite <- H.
Qed.

Add Parametric Morphism : perm_disj_list
  with signature @Permutation Qc ==> iff
    as perm_disj_list_permut_mor.
Proof.
  intros xs ys ?. intuition.
  apply perm_disj_list_permutation with xs; auto.
  apply perm_disj_list_permutation with ys; auto.
Qed.

Lemma perm_disj_list_single :
  forall q, perm_disj_list [q] <-> perm_valid q.
Proof.
  unfold perm_disj_list, perm_valid.
  intro q. intuition simpls; desf.
  by rewrite <- Qcplus_0_r with q.
  by rewrite Qcplus_0_r.
Qed.

Hint Resolve perm_disj_list_single.

Lemma perm_disj_list_binary :
  forall q1 q2,
  perm_disj_list [q1; q2] <-> perm_disj q1 q2.
Proof.
  unfold perm_disj_list, perm_disj.
  intros q1 q2. intuition simpls; desf.
  by rewrite <- Qcplus_0_r with q2.
  by rewrite Qcplus_0_r.
Qed.

Lemma perm_disj_list_tail :
  forall q qs,
  perm_disj_list (q :: qs) -> perm_disj_list qs.
Proof.
  unfold perm_disj_list.
  intros q qs H. simpls. intuition.
  apply Qcplus_pos_le_elim with q.
  by rewrite Qcplus_comm.
  by apply Qclt_le_weak.
Qed.

Lemma perm_disj_list_sub_r :
  forall xs ys,
  perm_disj_list (xs ++ ys) -> perm_disj_list ys.
Proof.
  induction xs; intros ys H; simpls.
  apply IHxs. by apply perm_disj_list_tail in H.
Qed.

Lemma perm_disj_list_sub_l :
  forall xs ys,
  perm_disj_list (xs ++ ys) -> perm_disj_list xs.
Proof.
  intros xs ys H.
  rewrite Permutation_app_comm in H.
  by apply perm_disj_list_sub_r in H.
Qed.

Lemma perm_disj_list_remove :
  forall q xs ys,
  perm_disj_list (xs ++ q :: ys) -> perm_disj_list (xs ++ ys).
Proof.
  intros q xs ys H.
  rewrite perm_takeit_5 in H.
  by apply perm_disj_list_tail in H.
Qed.

Lemma perm_disj_list_remove_list :
  forall xs ys zs,
  perm_disj_list (xs ++ ys ++ zs) -> perm_disj_list (xs ++ zs).
Proof.
  intros xs ys zs H.
  rewrite perm_takeit_1 in H.
  by apply perm_disj_list_sub_r in H.
Qed.

Lemma perm_disj_list_add_left :
  forall q1 q2 qs,
  perm_disj_list (q1 :: q2 :: qs) -> perm_disj_list (q1 + q2 :: qs).
Proof.
  unfold perm_disj_list. intuition.
  by apply perm_pos_list_add_left.
  by rewrite <- perm_add_list_add_left.
Qed.

Lemma perm_disj_list_add :
  forall q1 q2 qs1 qs2,
  perm_disj_list (qs1 ++ q1 :: q2 :: qs2) ->
  perm_disj_list (qs1 ++ q1 + q2 :: qs2).
Proof.
  unfold perm_disj_list. intuition.
  by apply perm_pos_list_add.
  by rewrite <- perm_add_list_add.
Qed.

Lemma perm_disj_list_valid_head :
  forall q qs,
  perm_disj_list (q :: qs) -> perm_valid q.
Proof.
  intros q qs H.
  apply perm_disj_list_sub_l with [q] qs in H.
  by apply perm_disj_list_single.
Qed.

Lemma perm_disj_list_valid :
  forall qs, perm_disj_list qs -> perm_valid_list qs.
Proof.
  induction qs; intro H; simpls. split.
  by apply perm_disj_list_valid_head in H.
  apply IHqs. by apply perm_disj_list_tail in H.
Qed.

Lemma perm_disj_list_pos :
  forall qs,
  perm_disj_list qs -> perm_pos_list qs.
Proof.
  induction qs; ins; simpls; desf; intuition vauto.
  apply perm_disj_list_valid_head in H. auto.
  apply IHqs.
  by apply perm_disj_list_tail in H.
Qed.

Lemma perm_disj_list_elim_left :
  forall q1 q2 qs,
  perm_pos_list [q1; q2] ->
  perm_disj_list (q1 + q2 :: qs) ->
  perm_disj_list (q1 :: q2 :: qs).
Proof.
  unfold perm_disj_list.
  intros q1 q2 qs H1 H2. intuition.
  apply perm_pos_list_tail in H.
  replace (q1 :: q2 :: qs) with ([q1; q2] ++ qs); auto.
  by apply perm_pos_list_app. simpls.
  by rewrite Qcplus_assoc.
Qed.

Lemma perm_disj_list_elim :
  forall q1 q2 qs1 qs2,
  perm_pos_list [q1; q2] ->
  perm_disj_list (qs1 ++ q1 + q2 :: qs2) ->
  perm_disj_list (qs1 ++ q1 :: q2 :: qs2).
Proof.
  intros q1 q2 qs1 qs2 H1 H2.
  replace (qs1 ++ q1 :: q2 :: qs2) with (qs1 ++ [q1; q2] ++ qs2); auto.
  rewrite perm_takeit_1.
  apply perm_disj_list_elim_left; auto.
  by rewrite Permutation_middle.
Qed.

Lemma perm_disj_list_elim_remove_l :
  forall q1 q2 qs1 qs2,
  perm_pos_list [q1; q2] ->
  perm_disj_list (qs1 ++ q1 + q2 :: qs2) ->
  perm_disj_list (qs1 ++ q1 :: qs2).
Proof.
  intros q1 q2 qs1 qs2 H1 H2.
  apply perm_disj_list_remove with q2.
  apply perm_disj_list_elim.
  perm_pos_list_solve.
  by rewrite Qcplus_comm.
Qed.

Lemma perm_disj_list_elim_remove_r :
  forall q1 q2 qs1 qs2,
  perm_pos_list [q1; q2] ->
  perm_disj_list (qs1 ++ q1 + q2 :: qs2) ->
  perm_disj_list (qs1 ++ q2 :: qs2).
Proof.
  intros q1 q2 qs1 qs2 H1 H2.
  rewrite Qcplus_comm in H2.
  apply perm_disj_list_elim_remove_l in H2; auto.
  perm_pos_list_solve.
Qed.

Lemma perm_disj_list_assoc_left :
  forall q1 q2 q3 qs,
  perm_pos_list [q2; q3] ->
  perm_disj_list (q1 :: q2 + q3 :: qs) ->
  perm_disj_list (q1 + q2 :: q3 :: qs).
Proof.
  unfold perm_disj_list.
  intros q1 q2 q3 qs H1 H2.
  intuition; [|simpls].
  by apply perm_pos_list_assoc_l.
  by repeat rewrite Qcplus_assoc in *.
Qed.

Lemma perm_disj_list_assoc :
  forall q1 q2 q3 qs1 qs2,
  perm_pos_list [q2; q3] ->
  perm_disj_list (qs1 ++ q1 :: q2 + q3 :: qs2) ->
  perm_disj_list (qs1 ++ q1 + q2 :: q3 :: qs2).
Proof.
  intros q1 q2 q3 qs1 qs2 H1 H2.
  apply perm_disj_list_permutation with (q1 + q2 :: q3 :: qs1 ++ qs2).
  list_permutation.
  apply perm_disj_list_assoc_left; auto.
  apply perm_disj_list_permutation with (qs1 ++ q1 :: q2 + q3 :: qs2); vauto.
  list_permutation.
Qed.

Lemma perm_disj_list_sublist :
  forall xs ys,
  sublist Qc_eq_dec xs ys ->
  perm_disj_list ys ->
  perm_disj_list xs.
Proof.
  unfold perm_disj_list.
  intros xs ys H1 H2.
  desf. split.
  by apply perm_pos_list_sublist with ys.
  apply Qcle_trans with (perm_add_list ys); auto.
  by apply perm_add_list_sublist.
Qed.

Lemma perm_disj_list_lt :
  forall x y xs,
  perm_valid x ->
  x < y ->
  perm_disj_list (y :: xs) ->
  perm_disj_list (x :: xs).
Proof.
  intros x y xs H1 H2 H3.
  unfold perm_disj_list in *.
  destruct H3 as (H3 & H4). split; auto.
  (* positivity *)
  - simpl. unfold perm_valid in H1.
    destruct H1 as (H1 & _). intuition.
    simpl in H3. by destruct H3 as (_ & H3).
  (* addition *)
  - simpls. destruct H3 as (H3 & H5).
    apply Qcle_trans with (y + perm_add_list xs); auto.
    apply Qcplus_le_mono_r.
    by apply Qclt_le_weak.
Qed.

Lemma perm_disj_list_le :
  forall x y xs,
  perm_valid x ->
  x <= y ->
  perm_disj_list (y :: xs) ->
  perm_disj_list (x :: xs).
Proof.
  intros x y xs H1 H2 H3.
  apply Qcle_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  by apply perm_disj_list_lt with y.
Qed.

Ltac permlist_solve1_with id :=
  match goal with
    | [ H : perm_disj_list ?X |- perm_disj_list ?Y ] =>
        match H with
          | id => apply perm_disj_list_permutation with X; auto; list_permutation;
              fail "permlist_solve can not solve this system"
        end
    | [ |- _ ] => fail "permlist_solve can not be applied"
  end.

Ltac permlist_solve1 :=
  match goal with
    | [ H : perm_disj_list ?X |- perm_disj_list ?Y ] =>
        permlist_solve1_with H
    | [ |- _ ] => fail "permlist_solve can not be applied"
  end.

Ltac permlist_solve2_with id :=
  match goal with
    | [ H : perm_disj_list ?X |- perm_disj_list ?Y ] =>
      match H with
        | id => apply perm_disj_list_sublist with X;
          [repeat (simpls; desf; intuition)|auto];
          fail "permlist_solve can not solve this system"
      end
    | [ |- _ ] => fail "permlist_solve can not be applied"
  end.

Ltac permlist_solve2 :=
  match goal with
    | [ H : perm_disj_list ?X |- perm_disj_list ?Y ] =>
        permlist_solve2_with H
    | [ |- _ ] => fail "permlist_solve can not be applied"
  end.

Ltac permlist_solve :=
  try permlist_solve1;
  try permlist_solve2;
  fail "permlist_solve can not solve this system".

Tactic Notation "permlist_solve" "with" ident(H) :=
  try permlist_solve1_with H;
  try permlist_solve2_with H;
  fail "permlist_solve can not solve this system".

Ltac perm_disj_list_split :=
  match goal with
    | |- perm_disj_list [?q1+?q2] => apply perm_disj_list_add with (qs1:=[])(qs2:=[]); simpl
    | |- perm_disj_list [?q1+?q2;?a] => apply perm_disj_list_add with (qs1:=[])(qs2:=[a]); simpl
    | |- perm_disj_list [?a;?q1+?q2] => apply perm_disj_list_add with (qs1:=[a])(qs2:=[]); simpl
    | |- perm_disj_list [?q1+?q2;?a;?b] => apply perm_disj_list_add with (qs1:=[])(qs2:=[a;b]); simpl
    | |- perm_disj_list [?a;?q1+?q2;?b] => apply perm_disj_list_add with (qs1:=[a])(qs2:=[b]); simpl
    | |- perm_disj_list [?a;?b;?q1+?q2] => apply perm_disj_list_add with (qs1:=[a;b])(qs2:=[]); simpl
    | |- perm_disj_list [?q1+?q2;?a;?b;?c] => apply perm_disj_list_add with (qs1:=[])(qs2:=[a;b;c]); simpl
    | |- perm_disj_list [?a;?q1+?q2;?b;?c] => apply perm_disj_list_add with (qs1:=[a])(qs2:=[b;c]); simpl
    | |- perm_disj_list [?a;?b;?q1+?q2;?c] => apply perm_disj_list_add with (qs1:=[a;b])(qs2:=[c]); simpl
    | |- perm_disj_list [?a;?b;?c;?q1+?q2] => apply perm_disj_list_add with (qs1:=[a;b;c])(qs2:=[]); simpl
    | |- perm_disj_list [?q1+?q2;?a;?b;?c;?d] => apply perm_disj_list_add with (qs1:=[])(qs2:=[a;b;c;d]); simpl
    | |- perm_disj_list [?a;?q1+?q2;?b;?c;?d] => apply perm_disj_list_add with (qs1:=[a])(qs2:=[b;c;d]); simpl
    | |- perm_disj_list [?a;?b;?q1+?q2;?c;?d] => apply perm_disj_list_add with (qs1:=[a;b])(qs2:=[c;d]); simpl
    | |- perm_disj_list [?a;?b;?c;?q1+?q2;?d] => apply perm_disj_list_add with (qs1:=[a;b;c])(qs2:=[d]); simpl
    | |- perm_disj_list [?a;?b;?c;?d;?q1+?q2] => apply perm_disj_list_add with (qs1:=[a;b;c;d])(qs2:=[]); simpl
    | |- perm_disj_list [?q1+?q2;?a;?b;?c;?d;?e] => apply perm_disj_list_add with (qs1:=[])(qs2:=[a;b;c;d;e]); simpl
    | |- perm_disj_list [?a;?q1+?q2;?b;?c;?d;?e] => apply perm_disj_list_add with (qs1:=[a])(qs2:=[b;c;d;e]); simpl
    | |- perm_disj_list [?a;?b;?q1+?q2;?c;?d;?e] => apply perm_disj_list_add with (qs1:=[a;b])(qs2:=[c;d;e]); simpl
    | |- perm_disj_list [?a;?b;?c;?q1+?q2;?d;?e] => apply perm_disj_list_add with (qs1:=[a;b;c])(qs2:=[d;e]); simpl
    | |- perm_disj_list [?a;?b;?c;?d;?q1+?q2;?e] => apply perm_disj_list_add with (qs1:=[a;b;c;d])(qs2:=[e]); simpl
    | |- perm_disj_list [?a;?b;?c;?d;?e;?q1+?q2] => apply perm_disj_list_add with (qs1:=[a;b;c;d;e])(qs2:=[]); simpl
    | [ |- _ ] => fail "perm_disj_list_split can not be applied."
  end.

Ltac perm_disj_list_split_in id :=
  match goal with
    | H : perm_disj_list ?T |- _ =>
      match H with
        | id => match T with
            | [?q1+?q2] => apply perm_disj_list_elim with q1 q2 [] [] in H; simpl in H; auto
            | [?q1+?q2;?a] => apply perm_disj_list_elim with q1 q2 [] [a] in H; simpl in H; auto
            | [?a;?q1+?q2] => apply perm_disj_list_elim with q1 q2 [a] [] in H; simpl in H; auto
            | [?q1+?q2;?a;?b] => apply perm_disj_list_elim with q1 q2 [] [a;b] in H; simpl in H; auto
            | [?a;?q1+?q2;?b] => apply perm_disj_list_elim with q1 q2 [a] [b] in H; simpl in H; auto
            | [?a;?b;?q1+?q2] => apply perm_disj_list_elim with q1 q2 [a;b] [] in H; simpl in H; auto
            | [?q1+?q2;?a;?b;?c] => apply perm_disj_list_elim with q1 q2 [] [a;b;c] in H; simpl in H; auto
            | [?a;?q1+?q2;?b;?c] => apply perm_disj_list_elim with q1 q2 [a] [b;c] in H; simpl in H; auto
            | [?a;?b;?q1+?q2;?c] => apply perm_disj_list_elim with q1 q2 [a;b] [c] in H; simpl in H; auto
            | [?a;?b;?c;?q1+?q2] => apply perm_disj_list_elim with q1 q2 [a;b;c] [] in H; simpl in H; auto
            | [?q1+?q2;?a;?b;?c;?d] => apply perm_disj_list_elim with q1 q2 [] [a;b;c;d] in H; simpl in H; auto
            | [?a;?q1+?q2;?b;?c;?d] => apply perm_disj_list_elim with q1 q2 [a] [b;c;d] in H; simpl in H; auto
            | [?a;?b;?q1+?q2;?c;?d] => apply perm_disj_list_elim with q1 q2 [a;b] [c;d] in H; simpl in H; auto
            | [?a;?b;?c;?q1+?q2;?d] => apply perm_disj_list_elim with q1 q2 [a;b;c] [d] in H; simpl in H; auto
            | [?a;?b;?c;?d;?q1+?q2] => apply perm_disj_list_elim with q1 q2 [a;b;c;d] [] in H; simpl in H; auto
            | [?q1+?q2;?a;?b;?c;?d;?e] => apply perm_disj_list_elim with q1 q2 [] [a;b;c;d;e] in H; simpl in H; auto
            | [?a;?q1+?q2;?b;?c;?d;?e] => apply perm_disj_list_elim with q1 q2 [a] [b;c;d;e] in H; simpl in H; auto
            | [?a;?b;?q1+?q2;?c;?d;?e] => apply perm_disj_list_elim with q1 q2 [a;b] [c;d;e] in H; simpl in H; auto
            | [?a;?b;?c;?q1+?q2;?d;?e] => apply perm_disj_list_elim with q1 q2 [a;b;c] [d;e] in H; simpl in H; auto
            | [?a;?b;?c;?d;?q1+?q2;?e] => apply perm_disj_list_elim with q1 q2 [a;b;c;d] [e] in H; simpl in H; auto
            | [?a;?b;?c;?d;?e;?q1+?q2] => apply perm_disj_list_elim with q1 q2 [a;b;c;d;e] [] in H; simpl in H; auto
            | _ => fail "perm_disj_list_split_in can not be applied."
          end
        | _ => fail "perm_disj_list_split_in can not be applied."
      end
    | [ |- _ ] => fail "perm_disj_list_split_in can not be applied."
  end.

Tactic Notation "permlist_split" := perm_disj_list_split.

Tactic Notation "permlist_split" "in" ident(H) :=
  perm_disj_list_split_in H;
  try (apply perm_disj_list_pos; clear H; permlist_solve).

Ltac perm_disj_list_remove q id :=
  match goal with
    | H : perm_disj_list ?T |- _ =>
      match H with
        | id => match T with
            | [q] => apply perm_disj_list_remove_list with [] [q] [] in H; simpl in H
            | [q;?a] => apply perm_disj_list_remove_list with [] [q] [a] in H; simpl in H
            | [?a;q] => apply perm_disj_list_remove_list with [a] [q] [] in H; simpl in H
            | [q;?a;?b] => apply perm_disj_list_remove_list with [] [q] [a;b] in H; simpl in H
            | [?a;q;?b] => apply perm_disj_list_remove_list with [a] [q] [b] in H; simpl in H
            | [?a;?b;q] => apply perm_disj_list_remove_list with [a;b] [q] [] in H; simpl in H
            | [q;?a;?b;?c] => apply perm_disj_list_remove_list with [] [q] [a;b;c] in H; simpl in H
            | [?a;q;?b;?c] => apply perm_disj_list_remove_list with [a] [q] [b;c] in H; simpl in H
            | [?a;?b;q;?c] => apply perm_disj_list_remove_list with [a;b] [q] [c] in H; simpl in H
            | [?a;?b;?c;q] => apply perm_disj_list_remove_list with [a;b;c] [q] [] in H; simpl in H
            | [q;?a;?b;?c;?d] => apply perm_disj_list_remove_list with [] [q] [a;b;c;d] in H; simpl in H
            | [?a;q;?b;?c;?d] => apply perm_disj_list_remove_list with [a] [q] [b;c;d] in H; simpl in H
            | [?a;?b;q;?c;?d] => apply perm_disj_list_remove_list with [a;b] [q] [c;d] in H; simpl in H
            | [?a;?b;?c;q;?d] => apply perm_disj_list_remove_list with [a;b;c] [q] [d] in H; simpl in H
            | [?a;?b;?c;?d;q] => apply perm_disj_list_remove_list with [a;b;c;d] [q] [] in H; simpl in H
            | [q;?a;?b;?c;?d;?e] => apply perm_disj_list_remove_list with [] [q] [a;b;c;d;e] in H; simpl in H
            | [?a;q;?b;?c;?d;?e] => apply perm_disj_list_remove_list with [a] [q] [b;c;d;e] in H; simpl in H
            | [?a;?b;q;?c;?d;?e] => apply perm_disj_list_remove_list with [a;b] [q] [c;d;e] in H; simpl in H
            | [?a;?b;?c;q;?d;?e] => apply perm_disj_list_remove_list with [a;b;c] [q] [d;e] in H; simpl in H
            | [?a;?b;?c;?d;q;?e] => apply perm_disj_list_remove_list with [a;b;c;d] [q] [e] in H; simpl in H
            | [?a;?b;?c;?d;?e;q] => apply perm_disj_list_remove_list with [a;b;c;d;e] [q] [] in H; simpl in H
            | _ => fail "perm_disj_list_remove does not apply here."
          end
        | _ => fail "perm_disj_list_remove does not apply here."
      end
    | [ |- _ ] => fail "perm_disj_list_remove does not apply here."
  end.

Tactic Notation "permlist_remove" constr(q) "in" ident(H) := perm_disj_list_remove q H.
