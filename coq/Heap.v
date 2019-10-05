Require Import Equalities.
Require Import FunctionalExtensionality.
Require Import HahnBase.
Require Import List.
Require Import Permissions.
Require Import Permutation.
Require Import PermutationTactic.
Require Import Prerequisites.
Require Import Process.
Require Import QArith.
Require Import Qcanon.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.


(** * Heaps *)

(** ** Ordinary heaps *)

Definition Loc := Z.
Definition Val := Z.
Definition Heap := Loc -> option Val.
Definition heap_iden : Heap := fun _ => None.


(** *** Subheaps *)

(** A heap [h1] is a _subheap_ (or _embedding_) of [h2] if [h2] contains at least [h1], that is,
    if [h1 l = h2 l] for every heap location [l] such that [h1 l] is defined. *)

Definition heap_sub (h1 h2 : Heap) : Prop :=
  forall (l : Loc)(v : Val), h1 l = Some v -> h2 l = Some v.

(** [heap_sub] is a (non-strict) partial order over heaps. *)

Instance heap_sub_refl :
  Reflexive heap_sub.
Proof.
  red. ins. red. ins.
Qed.

Lemma heap_sub_antisymm :
  antisymmetric Heap heap_sub.
Proof.
  intros h1 h2 H1 H2. extensionality l.
  unfold heap_sub in H1, H2.
  remember (h1 l) as h1v. remember (h2 l) as h2v.
  destruct h1v as [v1|], h2v as [v2|]; vauto.
  - symmetry in Heqh1v, Heqh2v.
    apply H1 in Heqh1v. vauto.
  - symmetry in Heqh1v. apply H1 in Heqh1v. congruence.
  - symmetry in Heqh2v. apply H2 in Heqh2v. congruence.
Qed.

Instance heap_sub_trans :
  Transitive heap_sub.
Proof.
  intros h1 h2 h3 H1 H2. red. intros l v H3.
  apply H1 in H3. by apply H2 in H3.
Qed.


(** *** Heap agreement *)

(** The operation [heap_agrees] determines whether two given heaps [h1] and [h2]
    agree on their contents, meaning that, if [h1 l] and [h2 l] are both defined, for
    any heap location [l], then [h1 l = h2 l]. *)

Definition heap_agrees (h1 h2 : Heap) : Prop :=
  forall (l : Loc)(v1 v2 : Val), h1 l = Some v1 -> h2 l = Some v2 -> v1 = v2.

(** [heap_agrees] is a reflexive and symmetric relation over heaps (although not a transitive one). *)

Instance heap_agrees_refl :
  Reflexive heap_agrees.
Proof.
  intros h. red. intros l v1 v2 H1 H2. vauto.
Qed.

Instance heap_agrees_symm :
  Symmetric heap_agrees.
Proof.
  intros h1 h2 H1. red. intros l v1 v2 H2 H3.
  unfold heap_agrees in H1. symmetry. by apply H1 with l.
Qed.

Lemma heap_agrees_sub :
  forall h1 h2 : Heap,
  heap_sub h1 h2 -> heap_agrees h1 h2.
Proof.
  intros h1 h2 H1. red. intros l v1 v2 H2 H3.
  apply H1 in H2. vauto.
Qed.


(** *** Finiteness *)

(** A heap is _finite_ if all mappings that are not free can be mapped to some
    finite structure, in this case a list. *)

Definition heap_finite (h : Heap) : Prop :=
  exists xs : list Loc,
    forall l : Loc, h l <> None -> In l xs.

Lemma heap_finite_iden :
  heap_finite heap_iden.
Proof.
  red. exists nil. intros l H. vauto.
Qed.

(** The main property of interest of finite permission heaps, is that one can
    always find a mapping that is free. *)

Lemma heap_finite_free :
  forall h : Heap,
  heap_finite h ->
  exists l : Loc, h l = None.
Proof.
  intros h (ls & FIN).
  assert (H : exists l : Loc, ~ In l ls). { apply list_Z_max_notin. }
  destruct H as (l & H).
  specialize FIN with l.
  exists l. tauto.
Qed.

Lemma heap_finite_upd :
  forall h l v,
  heap_finite h ->
  heap_finite (update h l v).
Proof.
  intros ph l val (xs & FIN).
  assert (H1 : val = None \/ ~ val = None). { apply classic. }
  destruct H1 as [H1 | H1].
  (* [val] is free *)
  - exists xs. intros l' H2. apply FIN.
    unfold update in H2. desf.
  (* [val] is not free *)
  - exists (l :: xs).
    intros l' H2.
    specialize FIN with l'. simpls.
    unfold update in H2.
    destruct (Z.eq_dec l l') as [|H3]; vauto.
    right. by apply FIN.
Qed.


(** ** Permission heap cells *)

Inductive PermHeapCell :=
  | PHCfree
  | PHCstd(q:Qc)(v:Val)
  | PHCproc(q:Qc)(v:Val)
  | PHCact(q:Qc)(v v':Val)
  | PHCinvalid.

Add Search Blacklist "PermHeapCell_rect".
Add Search Blacklist "PermHeapCell_ind".
Add Search Blacklist "PermHeapCell_rec".


(** *** Validity *)

Definition phc_valid (phc : PermHeapCell) : Prop :=
  match phc with
    | PHCfree => True
    | PHCstd q _
    | PHCproc q _
    | PHCact q _ _ => perm_valid q
    | PHCinvalid => False
  end.

Notation "√ phc" := (phc_valid phc) (only printing, at level 80).

Lemma phc_valid_contra :
  forall phc,
  phc_valid phc -> phc <> PHCinvalid.
Proof.
  intros phc H. unfold phc_valid in H. desf.
Qed.

Hint Resolve phc_valid_contra.


(** *** Disjointness *)

Definition phc_disj (phc1 phc2 : PermHeapCell) : Prop :=
  match phc1, phc2 with
    | PHCinvalid, _
    | _, PHCinvalid => False
    | PHCfree, PHCfree => True
    | PHCfree, phc
    | phc, PHCfree => phc_valid phc
    | PHCstd q1 v1, PHCstd q2 v2 => perm_disj q1 q2 /\ v1 = v2
    | PHCstd _ _, _
    | _, PHCstd _ _ => False
    | PHCproc q1 v1, PHCproc q2 v2 => perm_disj q1 q2 /\ v1 = v2
    | PHCproc _ _, _
    | _, PHCproc _ _ => False
    | PHCact q1 v1 v1', PHCact q2 v2 v2' => perm_disj q1 q2 /\ v1 = v2 /\ v1' = v2'
  end.

Notation "phc1 ⟂ phc2" := (phc_disj phc1 phc2) (only printing, at level 80).

Instance phc_disj_symm :
  Symmetric phc_disj.
Proof.
  unfold phc_disj. red.
  ins; desf; simpls; intuition.
Qed.

Hint Resolve phc_disj_symm.

Lemma phc_disj_iden_l :
  forall phc,
  phc_valid phc -> phc_disj phc PHCfree.
Proof.
  ins. red. desf.
Qed.

Hint Resolve phc_disj_iden_l.

Lemma phc_disj_iden_r :
  forall phc,
  phc_valid phc -> phc_disj PHCfree phc.
Proof.
  ins. desf.
Qed.

Hint Resolve phc_disj_iden_r.

Lemma phc_disj_valid_l :
  forall phc1 phc2,
  phc_disj phc1 phc2 -> phc_valid phc1.
Proof.
  unfold phc_disj, phc_valid.
  intros ?? H.
  repeat desf; try (by apply perm_disj_valid in H; desf).
Qed.

Lemma phc_disj_valid_r :
  forall phc1 phc2,
  phc_disj phc1 phc2 -> phc_valid phc2.
Proof.
  intros ?? H. symmetry in H.
  by apply phc_disj_valid_l in H.
Qed.

Lemma phc_disj_valid :
  forall phc1 phc2,
  phc_disj phc1 phc2 -> phc_valid phc1 /\ phc_valid phc2.
Proof.
  intros phc1 phc2 H. split.
  - by apply phc_disj_valid_l in H.
  - by apply phc_disj_valid_r in H.
Qed.


(** *** Addition *)


Lemma Val_pair_eq_dec :
  forall x y : Val * Val, {x = y} + {x <> y}.
Proof.
  decide equality; apply Z.eq_dec.
Qed.

Definition phc_add (phc1 phc2 : PermHeapCell) : PermHeapCell :=
  match phc1, phc2 with
    | PHCinvalid, _
    | _, PHCinvalid => PHCinvalid
    | PHCfree, phc
    | phc, PHCfree => phc
    | PHCstd q1 v1, PHCstd q2 v2 =>
      if Z.eq_dec v1 v2 then PHCstd (q1 + q2) v1 else PHCinvalid
    | PHCstd _ _, _
    | _, PHCstd _ _ => PHCinvalid
    | PHCproc q1 v1, PHCproc q2 v2 =>
      if Z.eq_dec v1 v2 then PHCproc (q1 + q2) v1 else PHCinvalid
    | PHCproc _ _, _
    | _, PHCproc _ _ => PHCinvalid
    | PHCact q1 v1 v1', PHCact q2 v2 v2' =>
      if Val_pair_eq_dec (v1, v1') (v2, v2') then PHCact (q1 + q2) v1 v1' else PHCinvalid
  end.

Notation "phc1 ⊕ phc2" := (phc_add phc1 phc2) (only printing, at level 80, right associativity).

Lemma phc_add_assoc :
  forall phc1 phc2 phc3,
  phc_add phc1 (phc_add phc2 phc3) =
  phc_add (phc_add phc1 phc2) phc3.
Proof.
  intros phc1 phc2 phc3.
  destruct phc1, phc2, phc3; simpls; desf;
    unfold phc_add; desf; by rewrite Qcplus_assoc.
Qed.

Lemma phc_add_comm :
  forall phc1 phc2,
  phc_add phc1 phc2 = phc_add phc2 phc1.
Proof.
  unfold phc_add. ins.
  repeat desf; by rewrite Qcplus_comm.
Qed.

Hint Resolve phc_add_comm.

Lemma phc_add_valid :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_valid (phc_add phc1 phc2).
Proof.
  unfold phc_disj, phc_add, phc_valid.
  ins. repeat desf; by apply perm_add_valid.
Qed.

Lemma phc_add_iden_l :
  forall phc, phc_add phc PHCfree = phc.
Proof.
  unfold phc_add. ins. desf.
Qed.

Hint Rewrite phc_add_iden_l.

Lemma phc_add_iden_r :
  forall phc, phc_add PHCfree phc = phc.
Proof.
  unfold phc_add. ins. desf.
Qed.

Hint Rewrite phc_add_iden_r.

Lemma phc_disj_add_l :
  forall phc1 phc2 phc3,
  phc_disj phc1 phc2 ->
  phc_disj (phc_add phc1 phc2) phc3 ->
  phc_disj phc2 phc3.
Proof.
  intros ??? H1 H2.
  unfold phc_add, phc_disj in *.
  desf; simpls; intuition vauto;
    try by apply perm_disj_valid_r in H.
  - apply perm_disj_list_binary in H.
    apply perm_disj_list_binary in H1.
    permlist_split in H1; auto.
    permlist_remove q2 in H1.
    by apply perm_disj_list_binary.
  - apply perm_disj_list_binary in H.
    apply perm_disj_list_binary in H1.
    permlist_split in H1; auto.
    permlist_remove q2 in H1.
    by apply perm_disj_list_binary.
  - apply perm_disj_list_binary in H.
    apply perm_disj_list_binary in H1.
    permlist_split in H1; auto.
    permlist_remove q2 in H1.
    by apply perm_disj_list_binary.
Qed.

Lemma phc_disj_add_r :
  forall phc1 phc2 phc3,
  phc_disj phc2 phc3 ->
  phc_disj phc1 (phc_add phc2 phc3) ->
  phc_disj phc1 phc2.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  symmetry in H1, H2.
  rewrite phc_add_comm in H2; auto.
  apply phc_disj_add_l in H2; auto.
Qed.

Lemma phc_disj_assoc_l :
  forall phc1 phc2 phc3,
  phc_disj phc1 phc2 ->
  phc_disj (phc_add phc1 phc2) phc3 ->
  phc_disj phc1 (phc_add phc2 phc3).
Proof.
  unfold phc_disj, phc_add.
  intros phc1 phc2 phc3 H1 H2.
  desf; simpls; intuition vauto.
  - apply perm_disj_list_single.
    permlist_split. by apply perm_disj_list_binary.
  - apply perm_disj_list_single.
    permlist_split. by apply perm_disj_list_binary.
  - apply perm_disj_list_single.
    permlist_split. by apply perm_disj_list_binary.
  - by apply perm_disj_assoc_l.
  - by apply perm_disj_assoc_l.
  - by apply perm_disj_assoc_l.
Qed.

Lemma phc_disj_assoc_r :
  forall phc1 phc2 phc3,
  phc_disj phc2 phc3 ->
  phc_disj phc1 (phc_add phc2 phc3) ->
  phc_disj (phc_add phc1 phc2) phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  symmetry in H1, H2.
  rewrite phc_add_comm in H2; auto.
  apply phc_disj_assoc_l in H2; auto.
  rewrite phc_add_comm in H2; auto.
Qed.

Lemma phc_disj_middle :
  forall phc1 phc2 phc3 phc4,
  phc_disj phc1 phc2 ->
  phc_disj phc3 phc4 ->
  phc_disj (phc_add phc1 phc2) (phc_add phc3 phc4) ->
  phc_disj phc2 phc3.
Proof.
  intros phc1 phc2 phc3 phc4 H1 H2 H3.
  apply phc_disj_add_l with phc1; auto.
  by apply phc_disj_add_r with phc4.
Qed.

Lemma phc_disj_compat :
  forall phc1 phc2 phc3 phc4,
  phc_disj phc1 phc3 ->
  phc_disj phc2 phc4 ->
  phc_disj (phc_add phc1 phc3) (phc_add phc2 phc4) ->
  phc_disj (phc_add phc1 phc2) (phc_add phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 H1 H2 H3.
  apply phc_disj_assoc_r.
  rewrite phc_add_comm.
  apply phc_disj_assoc_l; auto.
  symmetry. by apply phc_disj_add_l in H3.
  rewrite phc_add_comm.
  rewrite <- phc_add_assoc.
  apply phc_disj_assoc_l; auto.
  by rewrite phc_add_comm with phc4 phc2.
Qed.

Lemma phc_add_swap_l :
  forall phc1 phc2 phc3,
  phc_add phc1 (phc_add phc2 phc3) =
  phc_add phc2 (phc_add phc1 phc3).
Proof.
  intros phc1 phc2 phc3.
  rewrite phc_add_assoc.
  rewrite phc_add_comm with phc1 phc2.
  by rewrite phc_add_assoc.
Qed.

Lemma phc_add_swap_r :
  forall phc1 phc2 phc3,
  phc_add (phc_add phc1 phc2) phc3 =
  phc_add (phc_add phc1 phc3) phc2.
Proof.
  intros phc1 phc2 phc3.
  rewrite phc_add_comm.
  rewrite phc_add_swap_l.
  by rewrite phc_add_assoc.
Qed.

Lemma phc_add_compat :
  forall phc1 phc2 phc3 phc4,
  phc_add (phc_add phc1 phc3) (phc_add phc2 phc4) =
  phc_add (phc_add phc1 phc2) (phc_add phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4.
  rewrite phc_add_swap_l.
  repeat rewrite phc_add_assoc.
  by rewrite phc_add_comm with phc2 phc1.
Qed.

Lemma phc_iden_split :
  forall phc1 phc2,
  phc_add phc1 phc2 = PHCfree ->
  phc1 = PHCfree /\ phc2 = PHCfree.
Proof.
  intros phc1 phc2 H.
  unfold phc_add in H. desf.
Qed.

Lemma phc_add_not_free :
  forall phc1 phc2,
  phc_add phc1 phc2 <> PHCfree <->
  phc1 <> PHCfree \/ phc2 <> PHCfree.
Proof.
  intros phc1 phc2. split; intro H.
  - unfold phc_add in H. desf; vauto.
  - unfold phc_add. desf; vauto.
Qed.


(** *** Ordering *)

(** The following (strict) partial order defines the 'less than'
    relation on permission heap cells. *)

Definition phc_lt (phc1 phc2 : PermHeapCell) : Prop :=
  match phc1, phc2 with
    | PHCfree, PHCfree => False
    | PHCfree, _ => True
    | PHCstd q1 v1, PHCstd q2 v2
    | PHCproc q1 v1, PHCproc q2 v2 => q1 < q2 /\ v1 = v2
    | PHCact q1 v1 v1', PHCact q2 v2 v2' => q1 < q2 /\ v1 = v2 /\ v1' = v2'
    | _, _ => False
  end.

Notation "phc1 ≺ phc2" := (phc_lt phc1 phc2) (only printing, at level 80).

Lemma phc_lt_irrefl :
  forall phc, ~ phc_lt phc phc.
Proof.
  intros phc H. unfold phc_lt in H.
  repeat desf.
  - by apply Qclt_irrefl with q.
  - by apply Qclt_irrefl with q.
  - by apply Qclt_irrefl with q.
Qed.

Instance phc_lt_trans :
  Transitive phc_lt.
Proof.
  red. intros phc1 phc2 phc3 H1 H2.
  unfold phc_lt in *.
  repeat desf; intuition vauto.
  - by apply Qclt_trans with q1.
  - by apply Qclt_trans with q1.
  - by apply Qclt_trans with q1.
Qed.

Lemma phc_lt_asymm :
  forall phc1 phc2,
  phc_lt phc1 phc2 -> ~ phc_lt phc2 phc1.
Proof.
  intros phc1 phc2 H1 H2.
  assert (H3 : phc_lt phc1 phc1). { by transitivity phc2. }
  by apply phc_lt_irrefl in H3.
Qed.

Lemma phc_lt_mono_pos :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_lt PHCfree phc2 ->
  phc_lt phc1 (phc_add phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phc_disj, phc_valid in H1.
  unfold phc_lt in *. unfold phc_add.
  repeat desf; simpls; intuition vauto.
  - apply Qclt_mono_pos. apply perm_disj_valid_r in H1. auto.
  - apply Qclt_mono_pos. apply perm_disj_valid_r in H1. auto.
  - apply Qclt_mono_pos. apply perm_disj_valid_r in H1. auto.
Qed.

Lemma phc_lt_mono_l :
  forall phc1 phc2 phc3,
  phc_disj phc3 phc2 ->
  phc_lt phc1 phc2 ->
  phc_lt (phc_add phc3 phc1) (phc_add phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  destruct phc3; vauto.
  (* [phc3] is free *)
  - by repeat rewrite phc_add_iden_r.
  (* [phc3] is a standard heap cell *)
  - unfold phc_disj, phc_add, phc_lt in *.
    repeat desf; intuition.
    + apply Qclt_mono_pos.
      apply perm_disj_valid_r in H1. auto.
    + by apply Qcplus_lt_mono_l.
  (* [phc3] is a process heap cell *)
  - unfold phc_disj, phc_add, phc_lt in *.
    repeat desf; intuition.
    + apply Qclt_mono_pos. apply perm_disj_valid_r in H1. auto.
    + by apply Qcplus_lt_mono_l.
  (* [phc3] is an action heap cell *)
  - unfold phc_disj, phc_add, phc_lt in *.
    repeat desf; intuition.
    + apply Qclt_mono_pos. apply perm_disj_valid_r in H1. auto.
    + by apply Qcplus_lt_mono_l.
Qed.

Lemma phc_lt_mono_r :
  forall phc1 phc2 phc3,
  phc_disj phc2 phc3 ->
  phc_lt phc1 phc2 ->
  phc_lt (phc_add phc1 phc3) (phc_add phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  rewrite phc_add_comm with phc1 phc3.
  rewrite phc_add_comm with phc2 phc3.
  apply phc_lt_mono_l; auto.
Qed.

Lemma phc_lt_diff :
  forall phc1 phc2,
  phc_valid phc1 ->
  phc_valid phc2 ->
  phc_lt phc1 phc2 ->
  exists phc3, phc_disj phc1 phc3 /\ phc_add phc1 phc3 = phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  unfold phc_valid in H1, H2.
  unfold phc_lt in H3. repeat desf; vauto.
  (* [phc1] is free and [phc2] a 'standard' cell *)
  - exists (PHCstd q v). vauto.
  (* [phc1] is free and [phc2] a 'process' cell *)
  - exists (PHCproc q v). vauto.
  (* [phc1] is free and [phc2] an 'action' cell *)
  - exists (PHCact q v v'). vauto.
  (* [phc1] and [phc2] are both 'standard' cells *)
  - apply perm_lt_diff in H3; auto.
    destruct H3 as (q' & H3 & H4); vauto.
    exists (PHCstd q' v0). intuition vauto.
    unfold phc_add. desf.
  (* [phc1] and [phc2] are both 'process' cells *)
  - apply perm_lt_diff in H3; auto.
    destruct H3 as (q' & H3 & H4); vauto.
    exists (PHCproc q' v0). intuition vauto.
    unfold phc_add. desf.
  (* [phc1] and [phc2] are both 'action' cells *)
  - apply perm_lt_diff in H3; vauto.
    destruct H3 as (q' & H3 & H4); vauto.
    exists (PHCact q' v0 v'0). intuition vauto.
    unfold phc_add. desf.
Qed.

Lemma phc_disj_lt :
  forall phc1 phc2 phc3,
  phc_valid phc1 ->
  phc_disj phc2 phc3 ->
  phc_lt phc1 phc2 ->
  phc_disj phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  generalize H2. intros H4.
  apply phc_disj_valid in H4.
  destruct H4 as (H4 & H5).
  unfold phc_lt in H3.
  unfold phc_disj, phc_valid in *.
  repeat desf; intuition vauto.
  - by apply perm_disj_lt with q1.
  - by apply perm_disj_lt with q1.
  - by apply perm_disj_lt with q1.
Qed.

(** The following partial order defines the 'less than or equal to'
    relation on permission heap cells. *)

Definition phc_le (phc1 phc2 : PermHeapCell) : Prop :=
  match phc1, phc2 with
    | PHCfree, _ => True
    | PHCstd q1 v1, PHCstd q2 v2
    | PHCproc q1 v1, PHCproc q2 v2 => q1 <= q2 /\ v1 = v2
    | PHCact q1 v1 v1', PHCact q2 v2 v2' => q1 <= q2 /\ v1 = v2 /\ v1' = v2'
    | PHCinvalid, PHCinvalid => True
    | _, _ => False
  end.

Notation "phc1 ≼ phc2" := (phc_le phc1 phc2) (only printing, at level 80).

Lemma phc_lt_le_weak :
  forall phc1 phc2,
  phc_lt phc1 phc2 -> phc_le phc1 phc2.
Proof.
  intros phc1 phc2 H.
  unfold phc_lt in H.
  unfold phc_le. repeat desf; intuition vauto.
  - by apply Qclt_le_weak.
  - by apply Qclt_le_weak.
  - by apply Qclt_le_weak.
Qed.

Instance phc_le_refl :
  Reflexive phc_le.
Proof.
  red. intro phc. red.
  repeat desf; intuition vauto; by apply Qcle_refl.
Qed.

Hint Resolve phc_le_refl.

Lemma phc_le_lt_or_eq :
  forall phc1 phc2,
  phc_le phc1 phc2 <->
  phc1 = phc2 \/ phc_lt phc1 phc2.
Proof.
  intros phc1 phc2. split; intro H.
  (* left to right *)
  - unfold phc_le in H. repeat desf; vauto.
    + destruct phc2; vauto.
    + apply Qcle_lt_or_eq in H. desf; vauto.
    + apply Qcle_lt_or_eq in H. desf; vauto.
    + apply Qcle_lt_or_eq in H. desf; vauto.
  (* right to left *)
  - destruct H as [H | H]; vauto.
    by apply phc_lt_le_weak.
Qed.

Lemma phc_le_antisym :
  forall phc1 phc2,
  phc_le phc1 phc2 -> phc_le phc2 phc1 -> phc1 = phc2.
Proof.
  intros phc1 phc2 H1 H2.
  apply phc_le_lt_or_eq in H1.
  apply phc_le_lt_or_eq in H2.
  destruct H1 as [H1 | H1], H2 as [H2 | H2]; vauto.
  by apply phc_lt_asymm in H1.
Qed.

Instance phc_le_trans :
  Transitive phc_le.
Proof.
  red. intros phc1 phc2 phc3 H1 H2.
  apply phc_le_lt_or_eq in H1.
  apply phc_le_lt_or_eq in H2.
  destruct H1 as [H1 | H1], H2 as [H2 | H2]; vauto.
  - by apply phc_lt_le_weak.
  - by apply phc_lt_le_weak.
  - apply phc_lt_le_weak.
    by transitivity phc2.
Qed.

Lemma phc_le_valid :
  forall phc,
  phc_le PHCfree phc.
Proof.
  ins.
Qed.

Lemma phc_le_lt_trans :
  forall phc1 phc2 phc3,
  phc_le phc1 phc2 ->
  phc_lt phc2 phc3 ->
  phc_lt phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phc_le_lt_or_eq in H1.
  destruct H1 as [H1 | H1]; vauto.
  by transitivity phc2.
Qed.

Lemma phc_lt_le_trans :
  forall phc1 phc2 phc3,
  phc_lt phc1 phc2 ->
  phc_le phc2 phc3 ->
  phc_lt phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phc_le_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  by transitivity phc2.
Qed.

Lemma phc_lt_weaken :
  forall phc1 phc2 phc3,
  phc_disj phc2 phc3 ->
  phc_lt phc1 phc2 ->
  phc_lt phc1 (phc_add phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phc_lt_le_trans with phc2; auto.
  assert (H3 : PHCfree = phc3 \/ phc_lt PHCfree phc3). {
  apply phc_le_lt_or_eq, phc_le_valid. }
  destruct H3 as [H3 | H3].
  (* [phc3] is free *)
  - clarify. by rewrite phc_add_iden_l.
  (* [phc3] is occupied *)
  - rewrite phc_le_lt_or_eq. right.
    by apply phc_lt_mono_pos.
Qed.

Lemma phc_le_weaken :
  forall phc1 phc2 phc3,
  phc_disj phc2 phc3 ->
  phc_le phc1 phc2 ->
  phc_le phc1 (phc_add phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phc_le_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  (* the 'equals' case *)
  - assert (H2 : PHCfree = phc3 \/ phc_lt PHCfree phc3). {
    apply phc_le_lt_or_eq, phc_le_valid. }
    destruct H2 as [H2 | H2].
    + clarify. by rewrite phc_add_iden_l.
    + apply phc_lt_le_weak.
      by apply phc_lt_mono_pos.
  (* the 'less than' case *)
  - by apply phc_lt_le_weak, phc_lt_weaken.
Qed.

Lemma phc_le_mono_l :
  forall phc1 phc2 phc3,
  phc_disj phc3 phc2 ->
  phc_le phc1 phc2 ->
  phc_le (phc_add phc3 phc1) (phc_add phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  apply phc_le_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  apply phc_lt_le_weak.
  by apply phc_lt_mono_l.
Qed.

Lemma phc_le_mono_r :
  forall phc1 phc2 phc3,
  phc_disj phc2 phc3 ->
  phc_le phc1 phc2 ->
  phc_le (phc_add phc1 phc3) (phc_add phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2.
  rewrite phc_add_comm with phc1 phc3.
  rewrite phc_add_comm with phc2 phc3.
  apply phc_le_mono_l; auto.
Qed.

Lemma phc_le_mono_pos :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_le phc1 (phc_add phc1 phc2).
Proof.
  intros phc1 phc2 H1.
  transitivity (phc_add phc1 PHCfree).
  - by rewrite phc_add_iden_l.
  - apply phc_le_mono_l; vauto.
Qed.

Lemma phc_le_compat :
  forall phc1 phc2 phc3 phc4,
  phc_disj phc1 phc4 ->
  phc_disj phc3 phc4 ->
  phc_le phc1 phc3 ->
  phc_le phc2 phc4 ->
  phc_le (phc_add phc1 phc2) (phc_add phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4.
  transitivity (phc_add phc1 phc4).
  apply phc_le_mono_l; auto.
  apply phc_le_mono_r; auto.
Qed.

Lemma phc_le_diff :
  forall phc1 phc2,
  phc_valid phc1 ->
  phc_valid phc2 ->
  phc_le phc1 phc2 ->
  exists phc3, phc_disj phc1 phc3 /\ phc_add phc1 phc3 = phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  apply phc_le_lt_or_eq in H3.
  destruct H3 as [H3 | H3]; clarify.
  (* the 'equals' case *)
  - exists PHCfree. split.
    + by apply phc_disj_iden_l.
    + by rewrite phc_add_iden_l.
  (* the 'less than' case *)
  - apply phc_lt_diff in H3; auto.
Qed.

Lemma phc_disj_le :
  forall phc1 phc2 phc3,
  phc_valid phc1 ->
  phc_disj phc2 phc3 ->
  phc_le phc1 phc2 ->
  phc_disj phc1 phc3.
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  apply phc_le_lt_or_eq in H3.
  destruct H3 as [H3 | H3]; vauto.
  by apply phc_disj_lt with phc2.
Qed.


(** *** Entirety *)

Definition phc_full (phc : PermHeapCell) : Prop :=
  match phc with
    | PHCfree
    | PHCinvalid => False
    | PHCstd q _
    | PHCproc q _
    | PHCact q _ _ => q = perm_full
  end.

Lemma phc_full_add_l :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_full phc1 ->
  phc_full (phc_add phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phc_disj in H1.
  unfold phc_full in *.
  unfold phc_add.
  repeat desf.
  - by apply perm_disj_full_neg_r in H1.
  - by apply perm_disj_full_neg_r in H1.
  - by apply perm_disj_full_neg_r in H1.
Qed.

Lemma phc_full_add :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_full phc1 \/ phc_full phc2 ->
  phc_full (phc_add phc1 phc2).
Proof.
  intros phc1 phc2 H1 H2.
  destruct H2 as [H2 | H2].
  - by apply phc_full_add_l.
  - rewrite phc_add_comm.
    apply phc_full_add_l; auto.
Qed.

Lemma phc_full_lt_neg :
  forall phc1 phc2,
  phc_valid phc2 ->
  phc_full phc1 ->
  ~ phc_lt phc1 phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  unfold phc_valid in H1.
  unfold phc_full in H2.
  unfold phc_lt in H3. repeat desf.
  - by apply perm_valid_full_neg in H3.
  - by apply perm_valid_full_neg in H3.
  - by apply perm_valid_full_neg in H3.
Qed.

Lemma phc_full_le :
  forall phc1 phc2,
  phc_le phc1 phc2 ->
  phc_valid phc2 ->
  phc_full phc1 ->
  phc_full phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  unfold phc_valid, perm_valid in H2.
  unfold phc_full, perm_full in *.
  desf; simpls; desf.
  - by apply Qcle_antisym.
  - by apply Qcle_antisym.
  - by apply Qcle_antisym.
Qed.

Lemma phc_le_full_eq :
  forall phc1 phc2,
  phc_valid phc2 ->
  phc_full phc1 ->
  phc_le phc1 phc2 ->
  phc1 = phc2.
Proof.
  intros phc1 phc2 H1 H2 H3.
  apply phc_le_lt_or_eq in H3.
  destruct H3 as [H3 | H3]; vauto.
  by apply phc_full_lt_neg in H3.
Qed.

Lemma phc_disj_full_free :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_full phc1 ->
  phc2 = PHCfree.
Proof.
  intros phc1 phc2 H1 H2.
  unfold phc_disj in H1.
  unfold phc_full in H2. repeat desf.
  - by apply perm_disj_full_neg_r in H1.
  - by apply perm_disj_full_neg_r in H1.
  - by apply perm_disj_full_neg_r in H1.
Qed.

Lemma phc_lt_full_free :
  forall phc,
  phc_full phc ->
  phc_lt PHCfree phc.
Proof.
  intros phc H.
  unfold phc_full in H.
  unfold phc_lt. desf.
Qed.


(** *** Concretisation *)

Definition phc_concr (phc : PermHeapCell) : option Val :=
  match phc with
    | PHCfree
    | PHCinvalid => None
    | PHCstd _ v
    | PHCproc _ v
    | PHCact _ v _ => Some v
  end.

Lemma phc_concr_lt_none :
  forall phc1 phc2,
  phc_lt phc1 phc2 ->
  phc_concr phc2 = None ->
  phc_concr phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  unfold phc_concr in *. desf.
Qed.

Lemma phc_concr_le_none :
  forall phc1 phc2,
  phc_le phc1 phc2 ->
  phc_concr phc2 = None ->
  phc_concr phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  apply phc_le_lt_or_eq in H1.
  destruct H1 as [H1 | H1]; vauto.
  by apply phc_concr_lt_none in H1.
Qed.

Lemma phc_concr_lt_some :
  forall phc1 phc2 v,
  phc_lt phc1 phc2 ->
  phc_concr phc1 = Some v ->
  phc_concr phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  unfold phc_concr in *.
  desf; simpls; desf.
Qed.

Lemma phc_concr_le_some :
  forall phc1 phc2 v,
  phc_le phc1 phc2 ->
  phc_concr phc1 = Some v ->
  phc_concr phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phc_le_lt_or_eq in H1.
  destruct H1 as [H1 | H1]; vauto.
  by apply phc_concr_lt_some with (v := v) in H1.
Qed.

Lemma phc_concr_none_free :
  forall phc,
  phc_valid phc ->
  phc_concr phc = None ->
  phc = PHCfree.
Proof.
  intros phc H1 H2. unfold phc_valid in H1.
  unfold phc_concr in H2. desf.
Qed.

Lemma phc_concr_add :
  forall phc1 phc2 v,
  phc_disj phc1 phc2 ->
  phc_concr phc1 = Some v ->
  phc_concr (phc_add phc1 phc2) = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phc_concr_le_some with phc1; vauto.
  by apply phc_le_mono_pos.
Qed.

Lemma phc_concr_compat :
  forall phc1 phc2 phc3 phc4 : PermHeapCell,
  phc_disj phc1 phc2 ->
  phc_disj phc3 phc4 ->
  phc_concr phc1 = phc_concr phc3 ->
  phc_concr phc2 = phc_concr phc4 ->
  phc_concr (phc_add phc1 phc2) = phc_concr (phc_add phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 D1 D2 H1 H2.
  unfold phc_disj, phc_add in *. repeat desf; vauto.
Qed.

Lemma phc_concr_disj_add_l :
  forall phc1 phc2 phc3,
  phc_disj phc1 phc3 ->
  phc_disj phc2 phc3 ->
  phc_concr phc1 = phc_concr phc2 ->
  phc_concr (phc_add phc1 phc3) = phc_concr (phc_add phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  apply phc_concr_compat; vauto.
Qed.

Lemma phc_concr_disj_add_r :
  forall phc1 phc2 phc3,
  phc_disj phc1 phc3 ->
  phc_disj phc2 phc3 ->
  phc_concr phc1 = phc_concr phc2 ->
  phc_concr (phc_add phc3 phc1) = phc_concr (phc_add phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  rewrite phc_add_comm with phc3 phc1.
  rewrite phc_add_comm with phc3 phc2.
  apply phc_concr_disj_add_l; auto.
Qed.


(** *** Snapshots *)

(** The following operation determines the _snapshot value_ of a given process heap cell. *)

Definition phc_snapshot (phc : PermHeapCell) : option Val :=
  match phc with
    | PHCfree
    | PHCinvalid
    | PHCstd _ _  => None
    | PHCproc _ v
    | PHCact _ _ v => Some v
  end.

Lemma phc_snapshot_compat :
  forall phc1 phc2 phc3 phc4 : PermHeapCell,
  phc_disj phc1 phc2 ->
  phc_disj phc3 phc4 ->
  phc_snapshot phc1 = phc_snapshot phc3 ->
  phc_snapshot phc2 = phc_snapshot phc4 ->
  phc_snapshot (phc_add phc1 phc2) = phc_snapshot (phc_add phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 D1 D2 H1 H2.
  unfold phc_disj, phc_add in *. repeat desf; vauto.
Qed.

Lemma phc_concr_snapshot_compat :
  forall phc1 phc2 phc3 phc4 : PermHeapCell,
  phc_disj phc1 phc2 ->
  phc_disj phc3 phc4 ->
  phc_concr phc1 = phc_snapshot phc3 ->
  phc_concr phc2 = phc_snapshot phc4 ->
  phc_concr (phc_add phc1 phc2) = phc_snapshot (phc_add phc3 phc4).
Proof.
  intros phc1 phc2 phc3 phc4 D1 D2 H1 H2.
  unfold phc_disj, phc_add in *. repeat desf; vauto.
Qed.

Lemma phc_snapshot_disj_add_l :
  forall phc1 phc2 phc3,
  phc_disj phc1 phc3 ->
  phc_disj phc2 phc3 ->
  phc_snapshot phc1 = phc_snapshot phc2 ->
  phc_snapshot (phc_add phc1 phc3) = phc_snapshot (phc_add phc2 phc3).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  apply phc_snapshot_compat; vauto.
Qed.

Lemma phc_snapshot_disj_add_r :
  forall phc1 phc2 phc3,
  phc_disj phc1 phc3 ->
  phc_disj phc2 phc3 ->
  phc_snapshot phc1 = phc_snapshot phc2 ->
  phc_snapshot (phc_add phc3 phc1) = phc_snapshot (phc_add phc3 phc2).
Proof.
  intros phc1 phc2 phc3 H1 H2 H3.
  rewrite phc_add_comm with phc3 phc1.
  rewrite phc_add_comm with phc3 phc2.
  apply phc_snapshot_disj_add_l; auto.
Qed.

Lemma phc_snapshot_lt_none :
  forall phc1 phc2,
  phc_lt phc1 phc2 ->
  phc_snapshot phc2 = None ->
  phc_snapshot phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  unfold phc_snapshot in *. desf.
Qed.

Lemma phc_snapshot_le_none :
  forall phc1 phc2,
  phc_le phc1 phc2 ->
  phc_snapshot phc2 = None ->
  phc_snapshot phc1 = None.
Proof.
  intros phc1 phc2 H1 H2.
  apply phc_le_lt_or_eq in H1.
  destruct H1 as [H1 | H1]; vauto.
  by apply phc_snapshot_lt_none in H1.
Qed.

Lemma phc_snapshot_lt_some :
  forall phc1 phc2 v,
  phc_lt phc1 phc2 ->
  phc_snapshot phc1 = Some v ->
  phc_snapshot phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  unfold phc_snapshot in *.
  desf; simpls; desf.
Qed.

Lemma phc_snapshot_le_some :
  forall phc1 phc2 v,
  phc_le phc1 phc2 ->
  phc_snapshot phc1 = Some v ->
  phc_snapshot phc2 = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phc_le_lt_or_eq in H1.
  destruct H1 as [H1 | H1]; vauto.
  by apply phc_snapshot_lt_some with (v := v) in H1.
Qed.

Lemma phc_snapshot_add :
  forall phc1 phc2 v,
  phc_disj phc1 phc2 ->
  phc_snapshot phc1 = Some v ->
  phc_snapshot (phc_add phc1 phc2) = Some v.
Proof.
  intros phc1 phc2 v H1 H2.
  apply phc_snapshot_le_some with phc1; vauto.
  by apply phc_le_mono_pos.
Qed.


(** *** Heap cell conversion *)

(** This section gives tools to convert the types of heap cells. *)

Definition phc_conv_std (phc : PermHeapCell) : PermHeapCell :=
  match phc with
    | PHCfree => PHCfree
    | PHCstd q v
    | PHCproc q v
    | PHCact q v _ => PHCstd q v
    | PHCinvalid => PHCinvalid
  end.

Definition phc_conv_proc (phc : PermHeapCell) : PermHeapCell :=
  match phc with
    | PHCfree => PHCfree
    | PHCstd q v
    | PHCproc q v
    | PHCact q v _ => PHCproc q v
    | PHCinvalid => PHCinvalid
  end.

Definition phc_conv_act (phc : PermHeapCell) : PermHeapCell :=
  match phc with
    | PHCfree => PHCfree
    | PHCstd q v
    | PHCproc q v => PHCact q v v
    | PHCact q v1 v2 => PHCact q v1 v2
    | PHCinvalid => PHCinvalid
  end.

Notation "'std' { phc }" := (phc_conv_std phc)(only printing, at level 40).
Notation "'proc' { phc }" := (phc_conv_proc phc)(only printing, at level 40).
Notation "'act' { phc }" := (phc_conv_act phc)(only printing, at level 40).

Lemma phc_std_conv :
  forall q v,
  PHCstd q v = phc_conv_std (PHCstd q v).
Proof.
  ins.
Qed.

Lemma phc_proc_conv :
  forall q v,
  PHCproc q v = phc_conv_proc (PHCproc q v).
Proof.
  ins.
Qed.

Lemma phc_act_conv :
  forall q v v',
  PHCact q v v' = phc_conv_act (PHCact q v v').
Proof.
  ins.
Qed.

Lemma phc_conv_std_idemp :
  forall phc,
  phc_conv_std (phc_conv_std phc) = phc_conv_std phc.
Proof.
  intro phc. unfold phc_conv_std. desf.
Qed.

Lemma phc_conv_proc_idemp :
  forall phc,
  phc_conv_proc (phc_conv_proc phc) = phc_conv_proc phc.
Proof.
  intro phc. unfold phc_conv_proc. desf.
Qed.

Lemma phc_conv_act_idemp :
  forall phc,
  phc_conv_act (phc_conv_act phc) = phc_conv_act phc.
Proof.
  intro phc. unfold phc_conv_act. desf.
Qed.

Lemma phc_conv_std_free :
  forall phc,
  phc = PHCfree ->
  phc_conv_std phc = phc.
Proof.
  unfold phc_conv_std.
  intuition desf.
Qed.

Lemma phc_conv_proc_free :
  forall phc,
  phc = PHCfree ->
  phc_conv_proc phc = phc.
Proof.
  unfold phc_conv_proc.
  intuition desf.
Qed.

Lemma phc_conv_act_free :
  forall phc,
  phc = PHCfree ->
  phc_conv_act phc = phc.
Proof.
  unfold phc_conv_act.
  intuition desf.
Qed.

Lemma phc_conv_std_free2 :
  forall phc,
  phc_conv_std phc = PHCfree <-> phc = PHCfree.
Proof.
  unfold phc_conv_std.
  intuition desf.
Qed.

Lemma phc_conv_proc_free2 :
  forall phc,
  phc_conv_proc phc = PHCfree <-> phc = PHCfree.
Proof.
  unfold phc_conv_proc.
  intuition desf.
Qed.

Lemma phc_conv_act_free2 :
  forall phc,
  phc_conv_act phc = PHCfree <-> phc = PHCfree.
Proof.
  unfold phc_conv_act.
  intuition desf.
Qed.

Lemma phc_conv_std_valid :
  forall phc,
  phc_valid phc ->
  phc_valid (phc_conv_std phc).
Proof.
  intros phc H. red. unfold phc_valid in H.
  unfold phc_conv_std. desf.
Qed.

Lemma phc_conv_proc_valid :
  forall phc,
  phc_valid phc ->
  phc_valid (phc_conv_proc phc).
Proof.
  intros phc H. red. unfold phc_valid in H.
  unfold phc_conv_proc. desf.
Qed.

Lemma phc_conv_act_valid :
  forall phc,
  phc_valid phc ->
  phc_valid (phc_conv_act phc).
Proof.
  intros phc H. red. unfold phc_valid in H.
  unfold phc_conv_act. desf.
Qed.

Lemma phc_conv_std_disj :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_disj (phc_conv_std phc1) (phc_conv_std phc2).
Proof.
  intros phc1 phc2 H1.
  unfold phc_disj in *.
  unfold phc_conv_std.
  repeat desf; intuition simpls; auto.
Qed.

Lemma phc_conv_proc_disj :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_disj (phc_conv_proc phc1) (phc_conv_proc phc2).
Proof.
  intros phc1 phc2 H1.
  unfold phc_disj in *.
  unfold phc_conv_proc.
  repeat desf; intuition simpls; auto.
Qed.

Lemma phc_conv_act_disj :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_disj (phc_conv_act phc1) (phc_conv_act phc2).
Proof.
  intros phc1 phc2 H1.
  unfold phc_disj in *.
  unfold phc_conv_act.
  repeat desf; intuition simpls; auto.
Qed.

(* note: for the right-to-left implication the validity condition is not strictly neccessary. *)
Lemma phc_lt_conv_std_disj :
  forall phc2 phc3 q v,
  phc_valid phc2 ->
  phc_lt (PHCstd q v) phc2 ->
  phc_disj (phc_conv_std phc2) phc3 <->
  phc_disj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro D1.
  (* left to right *)
  - unfold phc_conv_std in D1. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
  (* right to left *)
  - unfold phc_conv_std. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
Qed.

(* note: for the right-to-left implication the validity condition is not strictly neccessary. *)
Lemma phc_lt_conv_proc_disj :
  forall phc2 phc3 q v,
  phc_valid phc2 ->
  phc_lt (PHCproc q v) phc2 ->
  phc_disj (phc_conv_proc phc2) phc3 <->
  phc_disj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro D1.
  (* left to right *)
  - unfold phc_conv_proc in D1. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
  (* right to left *)
  - unfold phc_conv_proc. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
Qed.

(* note: for the right-to-left implication the validity condition is not strictly neccessary. *)
Lemma phc_lt_conv_act_disj :
  forall phc2 phc3 q v1 v2,
  phc_valid phc2 ->
  phc_lt (PHCact q v1 v2) phc2 ->
  phc_disj (phc_conv_act phc2) phc3 <->
  phc_disj phc2 phc3.
Proof.
  intros phc2 phc3 q v1 v2 V1 H1. split; intro D1.
  (* left to right *)
  - unfold phc_conv_act in D1. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
  (* right to left *)
  - unfold phc_conv_act. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
Qed.

Lemma phc_le_conv_std_disj :
  forall phc2 phc3 q v,
  phc_valid phc2 ->
  phc_le (PHCstd q v) phc2 ->
  phc_disj (phc_conv_std phc2) phc3 <->
  phc_disj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro D1.
  (* left to right *)
  - unfold phc_conv_std in D1. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
  (* right to left *)
  - unfold phc_conv_std. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
Qed.

Lemma phc_le_conv_proc_disj :
  forall phc2 phc3 q v,
  phc_valid phc2 ->
  phc_le (PHCproc q v) phc2 ->
  phc_disj (phc_conv_proc phc2) phc3 <->
  phc_disj phc2 phc3.
Proof.
  intros phc2 phc3 q v V1 H1. split; intro D1.
  (* left to right *)
  - unfold phc_conv_proc in D1. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
  (* right to left *)
  - unfold phc_conv_proc. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
Qed.

Lemma phc_le_conv_act_disj :
  forall phc2 phc3 q v v',
  phc_valid phc2 ->
  phc_le (PHCact q v v') phc2 ->
  phc_disj (phc_conv_act phc2) phc3 <->
  phc_disj phc2 phc3.
Proof.
  intros phc2 phc3 q v v' V1 H1. split; intro D1.
  (* left to right *)
  - unfold phc_conv_act in D1. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
  (* right to left *)
  - unfold phc_conv_act. unfold phc_disj in *.
    repeat desf; simpls; intuition vauto.
Qed.

Lemma phc_conv_std_full :
  forall phc,
  phc_full (phc_conv_std phc) <->
  phc_full phc.
Proof.
  intros phc. split; intro H.
  (* left to right *)
  - unfold phc_full, phc_conv_std in *. desf.
  (* right to left *)
  - unfold phc_full, phc_conv_std in *. desf.
Qed.

Lemma phc_conv_proc_full :
  forall phc,
  phc_full (phc_conv_proc phc) <->
  phc_full phc.
Proof.
  intros phc. split; intro H.
  (* left to right *)
  - unfold phc_full, phc_conv_proc in *. desf.
  (* right to left *)
  - unfold phc_full, phc_conv_proc in *. desf.
Qed.

Lemma phc_conv_act_full :
  forall phc,
  phc_full (phc_conv_act phc) <->
  phc_full phc.
Proof.
  intros phc. split; intro H.
  (* left to right *)
  - unfold phc_full, phc_conv_act in *. desf.
  (* right to left *)
  - unfold phc_full, phc_conv_act in *. desf.
Qed.

Lemma phc_conv_std_disj_full :
  forall phc1 phc2,
  phc_full phc1 ->
  phc_disj phc1 phc2 ->
  phc_disj (phc_conv_std phc1) phc2.
Proof.
  intros phc1 phc2 H1 H2.
  assert (H3 : phc_valid phc1). { by apply phc_disj_valid_l in H2. }
  apply phc_disj_full_free in H2; auto. clarify.
  replace PHCfree with (phc_conv_std PHCfree); auto.
  by apply phc_conv_std_disj, phc_disj_iden_r.
Qed.

Lemma phc_conv_proc_disj_full :
  forall phc1 phc2,
  phc_full phc1 ->
  phc_disj phc1 phc2 ->
  phc_disj (phc_conv_proc phc1) phc2.
Proof.
  intros phc1 phc2 H1 H2.
  assert (H3 : phc_valid phc1). { by apply phc_disj_valid_l in H2. }
  apply phc_disj_full_free in H2; auto. clarify.
  replace PHCfree with (phc_conv_proc PHCfree); auto.
  by apply phc_conv_proc_disj, phc_disj_iden_r.
Qed.

Lemma phc_conv_act_disj_full :
  forall phc1 phc2,
  phc_full phc1 ->
  phc_disj phc1 phc2 ->
  phc_disj (phc_conv_act phc1) phc2.
Proof.
  intros phc1 phc2 H1 H2.
  assert (H3 : phc_valid phc1). { by apply phc_disj_valid_l in H2. }
  apply phc_disj_full_free in H2; auto. clarify.
  replace PHCfree with (phc_conv_act PHCfree); auto.
  by apply phc_conv_act_disj, phc_disj_iden_r.
Qed.

Lemma phc_conv_std_add :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_conv_std (phc_add phc1 phc2) =
  phc_add (phc_conv_std phc1) (phc_conv_std phc2).
Proof.
  intros phc1 phc2 H.
  unfold phc_disj in H.
  unfold phc_conv_std, phc_add.
  repeat desf.
Qed.

Lemma phc_conv_proc_add :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_conv_proc (phc_add phc1 phc2) =
  phc_add (phc_conv_proc phc1) (phc_conv_proc phc2).
Proof.
  intros phc1 phc2 H.
  unfold phc_disj in H.
  unfold phc_conv_proc, phc_add.
  repeat desf.
Qed.

Lemma phc_conv_act_add :
  forall phc1 phc2,
  phc_disj phc1 phc2 ->
  phc_conv_act (phc_add phc1 phc2) =
  phc_add (phc_conv_act phc1) (phc_conv_act phc2).
Proof.
  intros phc1 phc2 H.
  unfold phc_disj in H.
  unfold phc_conv_act, phc_add.
  repeat desf.
Qed.

Lemma phc_conv_std_lt :
  forall phc1 phc2,
  phc_valid phc2 ->
  phc_lt phc1 phc2 ->
  phc_lt (phc_conv_std phc1) (phc_conv_std phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phc_valid in H1.
  unfold phc_conv_std, phc_lt in *.
  repeat desf.
Qed.

(* note: this result does not hold for process- or action heap cells. *)
Lemma phc_conv_std_lt_eq :
  forall q v phc,
  phc_lt (PHCstd q v) phc ->
  phc = phc_conv_std phc.
Proof.
  intros q v phc H1. unfold phc_conv_std in *.
  unfold phc_lt in H1. desf.
Qed.

Lemma phc_conv_proc_lt :
  forall phc1 phc2,
  phc_valid phc2 ->
  phc_lt phc1 phc2 ->
  phc_lt (phc_conv_proc phc1) (phc_conv_proc phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phc_valid in H1.
  unfold phc_conv_proc, phc_lt in *.
  repeat desf.
Qed.

Lemma phc_conv_act_lt :
  forall phc1 phc2,
  phc_valid phc2 ->
  phc_lt phc1 phc2 ->
  phc_lt (phc_conv_act phc1) (phc_conv_act phc2).
Proof.
  intros phc1 phc2 H1 H2.
  unfold phc_valid in H1.
  unfold phc_conv_act, phc_lt in *.
  repeat desf.
Qed.

Lemma phc_conv_std_le :
  forall phc1 phc2,
  phc_valid phc2 ->
  phc_le phc1 phc2 ->
  phc_le (phc_conv_std phc1) (phc_conv_std phc2).
Proof.
  intros phc1 phc2 H1 H2.
  apply phc_le_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  by apply phc_lt_le_weak, phc_conv_std_lt.
Qed.

Lemma phc_conv_proc_le :
  forall phc1 phc2,
  phc_valid phc2 ->
  phc_le phc1 phc2 ->
  phc_le (phc_conv_proc phc1) (phc_conv_proc phc2).
Proof.
  intros phc1 phc2 H1 H2.
  apply phc_le_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  by apply phc_lt_le_weak, phc_conv_proc_lt.
Qed.

Lemma phc_conv_act_le :
  forall phc1 phc2,
  phc_valid phc2 ->
  phc_le phc1 phc2 ->
  phc_le (phc_conv_act phc1) (phc_conv_act phc2).
Proof.
  intros phc1 phc2 H1 H2.
  apply phc_le_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  by apply phc_lt_le_weak, phc_conv_act_lt.
Qed.

Lemma phc_conv_std_concr :
  forall phc,
  phc_concr (phc_conv_std phc) =
  phc_concr phc.
Proof.
  intro phc. unfold phc_concr, phc_conv_std. desf.
Qed.

Lemma phc_conv_proc_concr :
  forall phc,
  phc_concr (phc_conv_proc phc) =
  phc_concr phc.
Proof.
  intro phc. unfold phc_concr, phc_conv_proc. desf.
Qed.

Lemma phc_conv_act_concr :
  forall phc,
  phc_concr (phc_conv_act phc) =
  phc_concr phc.
Proof.
  intro phc. unfold phc_concr, phc_conv_act. desf.
Qed.

Lemma phc_snapshot_conv_proc_occ :
  forall phc,
  phc_snapshot phc <> None ->
  phc_snapshot (phc_conv_proc phc) <> None.
Proof.
  intros phc H1. unfold phc_snapshot in *.
  unfold phc_conv_proc. desf.
Qed.

Lemma phc_snapshot_conv_act_occ :
  forall phc,
  phc_snapshot phc <> None ->
  phc_snapshot (phc_conv_act phc) <> None.
Proof.
  intros phc H1. unfold phc_snapshot in *.
  unfold phc_conv_act. desf.
Qed.

Lemma phc_snapshot_lt_conv_std :
  forall phc1 phc2,
  phc_lt phc1 (phc_conv_std phc2) ->
  phc_snapshot phc1 = phc_snapshot (phc_conv_std phc1).
Proof.
  intros phc1 phc2 H1. unfold phc_conv_std in *.
  unfold phc_lt in H1. unfold phc_snapshot. desf.
Qed.

Lemma phc_snapshot_lt_conv_proc :
  forall phc1 phc2,
  phc_lt phc1 (phc_conv_proc phc2) ->
  phc_snapshot phc1 = phc_snapshot (phc_conv_proc phc1).
Proof.
  intros phc1 phc2 H1. unfold phc_conv_proc in *.
  unfold phc_lt in H1. unfold phc_snapshot. desf.
Qed.

Lemma phc_snapshot_lt_conv_act :
  forall phc1 phc2,
  phc_lt phc1 (phc_conv_act phc2) ->
  phc_snapshot phc1 = phc_snapshot (phc_conv_act phc1).
Proof.
  intros phc1 phc2 H1. unfold phc_conv_act in *.
  unfold phc_lt in H1. unfold phc_snapshot. desf.
Qed.

Lemma phc_snapshot_conv_act_pres :
  forall phc v,
  phc_snapshot phc = Some v ->
  phc_snapshot (phc_conv_act phc) = Some v.
Proof.
  intros phc v H. unfold phc_snapshot, phc_conv_act in *. desf.
Qed.


(** ** Permission heaps *)

Definition PermHeap := Loc -> PermHeapCell.
Definition permheap_iden : PermHeap := fun _ => PHCfree.


(** *** Validity *)

Definition permheap_valid (ph : PermHeap) : Prop :=
  forall l : Loc, phc_valid (ph l).

Notation "√ ph" := (permheap_valid ph) (only printing, at level 80).

Lemma permheap_valid_iden :
  permheap_valid permheap_iden.
Proof.
  red. ins.
Qed.

Hint Resolve permheap_valid_iden.

Lemma permheap_valid_upd :
  forall ph phc l,
  permheap_valid ph ->
  phc_valid phc ->
  permheap_valid (update ph l phc).
Proof.
  intros ??????. unfold update. desf.
Qed.


(** *** Disjointness *)

Definition permheap_disj (ph1 ph2 : PermHeap) : Prop :=
  forall l : Loc, phc_disj (ph1 l) (ph2 l).

Notation "ph1 ⟂ ph2" := (permheap_disj ph1 ph2) (only printing, at level 80).

Instance permheap_disj_symm :
  Symmetric permheap_disj.
Proof.
  intros ????. by symmetry.
Qed.

Hint Resolve permheap_disj_symm.

Lemma permheap_disj_valid_l :
  forall ph1 ph2,
  permheap_disj ph1 ph2 -> permheap_valid ph1.
Proof.
  intros ? ph ? l.
  by apply phc_disj_valid_l with (ph l).
Qed.

Lemma permheap_disj_valid_r :
  forall ph1 ph2,
  permheap_disj ph1 ph2 -> permheap_valid ph2.
Proof.
  intros ph ?? l.
  by apply phc_disj_valid_r with (ph l).
Qed.

Lemma permheap_disj_valid :
  forall ph1 ph2,
  permheap_disj ph1 ph2 -> permheap_valid ph1 /\ permheap_valid ph2.
Proof.
  intros ph1 ph2 H. intuition.
  by apply permheap_disj_valid_l with ph2.
  by apply permheap_disj_valid_r with ph1.
Qed.

Lemma permheap_disj_iden_l :
  forall ph,
  permheap_valid ph -> permheap_disj ph permheap_iden.
Proof.
  unfold permheap_valid, permheap_iden.
  intros ???. by apply phc_disj_iden_l.
Qed.

Hint Resolve permheap_disj_iden_l.

Lemma permheap_disj_iden_r :
  forall ph,
  permheap_valid ph -> permheap_disj permheap_iden ph.
Proof.
  unfold permheap_valid, permheap_iden.
  intros ???. by apply phc_disj_iden_r.
Qed.

Hint Resolve permheap_disj_iden_r.

Lemma permheap_disj_upd :
  forall ph1 ph2 phc1 phc2 l,
  phc_disj phc1 phc2 ->
  permheap_disj ph1 ph2 ->
  permheap_disj (update ph1 l phc1) (update ph2 l phc2).
Proof.
  unfold permheap_disj, update.
  intros ????????. desf.
Qed.


(** *** Addition *)

Definition permheap_add (ph1 ph2 : PermHeap) : PermHeap :=
  fun l : Loc => phc_add (ph1 l) (ph2 l).

Notation "A ⊕ B" := (permheap_add A B) (only printing, at level 80, right associativity).

Lemma permheap_add_iden_l :
  forall ph, permheap_add ph permheap_iden = ph.
Proof.
  intro ph. extensionality l.
  unfold permheap_add, permheap_iden.
  apply phc_add_iden_l.
Qed.

Hint Rewrite permheap_add_iden_l.

Lemma permheap_add_iden_r :
  forall ph, permheap_add permheap_iden ph = ph.
Proof.
  intro ph. extensionality l.
  unfold permheap_add, permheap_iden.
  apply phc_add_iden_r.
Qed.

Hint Rewrite permheap_add_iden_r.

Lemma permheap_add_assoc :
  forall ph1 ph2 ph3,
  permheap_add (permheap_add ph1 ph2) ph3 =
  permheap_add ph1 (permheap_add ph2 ph3).
Proof.
	intros ???. extensionality l.
  unfold permheap_add.
  by rewrite phc_add_assoc.
Qed.

Hint Resolve permheap_add_assoc.

Lemma permheap_add_comm :
  forall ph1 ph2,
  permheap_add ph1 ph2 = permheap_add ph2 ph1.
Proof.
  intros ??. extensionality l.
  by apply phc_add_comm.
Qed.

Lemma permheap_add_valid :
  forall ph1 ph2,
  permheap_disj ph1 ph2 -> permheap_valid (permheap_add ph1 ph2).
Proof.
  unfold permheap_add. intros ????.
  by apply phc_add_valid.
Qed.

Hint Resolve permheap_add_valid.

Lemma permheap_disj_add_l :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_add ph1 ph2) ph3 ->
  permheap_disj ph2 ph3.
Proof.
  intros ph1 ph2 ph3 H1 H2 l.
  apply phc_disj_add_l with (ph1 l); auto.
  by apply H2.
Qed.

Lemma permheap_disj_add_r :
  forall ph1 ph2 ph3,
  permheap_disj ph2 ph3 ->
  permheap_disj ph1 (permheap_add ph2 ph3) ->
  permheap_disj ph1 ph2.
Proof.
  intros ph1 ph2 ph3 H1 H2 l.
  apply phc_disj_add_r with (ph3 l); auto.
  by apply H2.
Qed.

Lemma permheap_disj_assoc_l :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_add ph1 ph2) ph3 ->
  permheap_disj ph1 (permheap_add ph2 ph3).
Proof.
  intros ???? H ?.
  apply phc_disj_assoc_l. auto. apply H.
Qed.

Lemma permheap_disj_assoc_r :
  forall ph1 ph2 ph3,
  permheap_disj ph2 ph3 ->
  permheap_disj ph1 (permheap_add ph2 ph3) ->
  permheap_disj (permheap_add ph1 ph2) ph3.
Proof.
  intros ???? H ?.
  apply phc_disj_assoc_r. auto. apply H.
Qed.

Lemma permheap_add_upd :
  forall ph1 ph2 phc1 phc2 l,
  update (permheap_add ph1 ph2) l (phc_add phc1 phc2) =
  permheap_add (update ph1 l phc1) (update ph2 l phc2).
Proof.
  ins. extensionality l'.
  unfold permheap_add, update. desf.
Qed.

Lemma permheap_add_cell :
  forall ph1 ph2 l,
  phc_add (ph1 l) (ph2 l) = permheap_add ph1 ph2 l.
Proof.
  ins.
Qed.

Lemma permheap_disj_middle :
  forall ph1 ph2 ph3 ph4,
  permheap_disj ph1 ph2 ->
  permheap_disj ph3 ph4 ->
  permheap_disj (permheap_add ph1 ph2) (permheap_add ph3 ph4) ->
  permheap_disj ph2 ph3.
Proof.
  intros ph1 ph2 ph3 ph4 H1 H2 H3.
  apply permheap_disj_add_l with ph1; auto.
  by apply permheap_disj_add_r with ph4.
Qed.

Lemma permheap_disj_compat :
  forall ph1 ph2 ph3 ph4,
  permheap_disj ph1 ph3 ->
  permheap_disj ph2 ph4 ->
  permheap_disj (permheap_add ph1 ph3) (permheap_add ph2 ph4) ->
  permheap_disj (permheap_add ph1 ph2) (permheap_add ph3 ph4).
Proof.
  intros ph1 ph2 ph3 ph4 H1 H2 H3.
  apply permheap_disj_assoc_r.
  rewrite permheap_add_comm.
  apply permheap_disj_assoc_l; auto.
  symmetry. by apply permheap_disj_add_l in H3.
  rewrite permheap_add_comm.
  rewrite permheap_add_assoc.
  apply permheap_disj_assoc_l; auto.
  by rewrite permheap_add_comm with ph4 ph2.
Qed.

Lemma permheap_add_swap_l :
  forall ph1 ph2 ph3,
  permheap_add ph1 (permheap_add ph2 ph3) =
  permheap_add ph2 (permheap_add ph1 ph3).
Proof.
  intros ph1 ph2 ph3.
  rewrite <- permheap_add_assoc.
  rewrite permheap_add_comm with ph1 ph2.
  by rewrite permheap_add_assoc.
Qed.

Lemma permheap_add_swap_r :
  forall ph1 ph2 ph3,
  permheap_add (permheap_add ph1 ph2) ph3 =
  permheap_add (permheap_add ph1 ph3) ph2.
Proof.
  intros ph1 ph2 ph3.
  rewrite permheap_add_comm.
  rewrite permheap_add_swap_l.
  by rewrite permheap_add_assoc.
Qed.

Lemma permheap_add_compat :
  forall ph1 ph2 ph3 ph4,
  permheap_add (permheap_add ph1 ph3) (permheap_add ph2 ph4) =
  permheap_add (permheap_add ph1 ph2) (permheap_add ph3 ph4).
Proof.
  intros ph1 ph2 ph3 ph4.
  rewrite permheap_add_swap_l.
  repeat rewrite <- permheap_add_assoc.
  by rewrite permheap_add_comm with ph2 ph1.
Qed.

Lemma permheap_add_upd_free :
  forall ph1 ph2 phc l,
  ph2 l = PHCfree ->
  permheap_add (update ph1 l phc) ph2 =
  update (permheap_add ph1 ph2) l phc.
Proof.
  intros ph1 ph2 phc l H1.
  extensionality l'.
  unfold update, permheap_add. desf.
  by rewrite H1, phc_add_iden_l.
Qed.


(** ** Concretisation *)

(** The following operation gives the _concrete heap_ of a given permission heap. *)

Definition permheap_concr (ph : PermHeap) : Heap :=
  fun l : Loc => phc_concr (ph l).

Lemma permheap_concr_upd :
  forall ph l phc,
  permheap_concr (update ph l phc) =
  update (permheap_concr ph) l (phc_concr phc).
Proof.
  intros ph l phc. extensionality l'.
  unfold permheap_concr, update. desf.
Qed.

Lemma permheap_concr_disj_add_l :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph3 ->
  permheap_disj ph2 ph3 ->
  permheap_concr ph1 = permheap_concr ph2 ->
  permheap_concr (permheap_add ph1 ph3) = permheap_concr (permheap_add ph2 ph3).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  extensionality l. unfold permheap_concr.
  repeat rewrite <- permheap_add_cell.
  apply phc_concr_disj_add_l; vauto.
  by apply equal_f with l in H3.
Qed.

Lemma permheap_concr_disj_add_r :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph3 ->
  permheap_disj ph2 ph3 ->
  permheap_concr ph1 = permheap_concr ph2 ->
  permheap_concr (permheap_add ph3 ph1) = permheap_concr (permheap_add ph3 ph2).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  rewrite permheap_add_comm with ph3 ph1.
  rewrite permheap_add_comm with ph3 ph2.
  apply permheap_concr_disj_add_l; auto.
Qed.


(** *** Snapshot *)

(** The following operation gives the _snapshot heap_ of a given permission heap. *)

Definition permheap_snapshot (ph : PermHeap) : Heap :=
  fun l : Loc => phc_snapshot (ph l).

Lemma permheap_snapshot_upd :
  forall ph l phc,
  permheap_snapshot (update ph l phc) =
  update (permheap_snapshot ph) l (phc_snapshot phc).
Proof.
  intros ph l phc. extensionality l'.
  unfold permheap_snapshot, update. desf.
Qed.

Lemma permheap_snapshot_disj_add_l :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph3 ->
  permheap_disj ph2 ph3 ->
  permheap_snapshot ph1 = permheap_snapshot ph2 ->
  permheap_snapshot (permheap_add ph1 ph3) = permheap_snapshot (permheap_add ph2 ph3).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  extensionality l. unfold permheap_snapshot.
  repeat rewrite <- permheap_add_cell.
  apply phc_snapshot_disj_add_l; vauto.
  by apply equal_f with l in H3.
Qed.

Lemma permheap_snapshot_disj_add_r :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph3 ->
  permheap_disj ph2 ph3 ->
  permheap_snapshot ph1 = permheap_snapshot ph2 ->
  permheap_snapshot (permheap_add ph3 ph1) = permheap_snapshot (permheap_add ph3 ph2).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  rewrite permheap_add_comm with ph3 ph1.
  rewrite permheap_add_comm with ph3 ph2.
  apply permheap_snapshot_disj_add_l; auto.
Qed.


(** *** Finiteness *)

(** A permission heap is _finite_ if all mappings that are not free can be mapped to some
    finite structure, in this case a list. *)

Definition permheap_finite (ph : PermHeap) : Prop :=
  exists xs : list Loc,
    forall l : Loc, ph l <> PHCfree -> In l xs.

(** The main property of interest of finite permission heaps, is that one can
    always find a mapping that is free. *)

Lemma permheap_finite_free :
  forall ph,
  permheap_finite ph ->
  exists l : Loc, ph l = PHCfree.
Proof.
  intros ph (xs & FIN).
  assert (H : exists l : Loc, ~ In l xs). {
  apply list_Z_max_notin. }
  destruct H as (l & H).
  specialize FIN with l.
  exists l. tauto.
Qed.

Lemma permheap_finite_upd :
  forall ph l phc,
  permheap_finite ph ->
  permheap_finite (update ph l phc).
Proof.
  intros ph l phc (xs & FIN).
  assert (H1 : phc = PHCfree \/ ~ phc = PHCfree). { apply classic. }
  destruct H1 as [H1 | H1].
  (* [phc] is free *)
  - exists xs. intros l' H2. apply FIN.
    unfold update in H2. desf.
  (* [phc] is not free *)
  - exists (l :: xs). intros l' H2.
    specialize FIN with l'. simpls.
    unfold update in H2.
    destruct (Z.eq_dec l l') as [|H3]; vauto.
    right. by apply FIN.
Qed.

Lemma permheap_finite_add :
  forall ph1 ph2,
  permheap_finite (permheap_add ph1 ph2) <->
  permheap_finite ph1 /\ permheap_finite ph2.
Proof.
  intros ph1 ph2. split.
  (* left to right *)
  - intros (xs & FIN).
    unfold permheap_finite. split.
    (* [ph1] is finite *)
    + exists xs. intros l H1.
      apply FIN. intro H2.
      apply phc_add_not_free in H2; vauto.
    (* [ph2] is finite *)
    + exists xs. intros l H1.
      apply FIN. intro H2.
      apply phc_add_not_free in H2; vauto.
  (* right to left *)
  - intro FIN.
    destruct FIN as ((xs1 & FIN1) & (xs2 & FIN2)).
    unfold permheap_finite.
    exists (xs1 ++ xs2). intros l H1.
    apply in_or_app.
    unfold permheap_add in H1.
    apply phc_add_not_free in H1.
    destruct H1 as [H1 | H1].
    + left. by apply FIN1.
    + right. by apply FIN2.
Qed.

Lemma permheap_finite_concr :
  forall ph,
  permheap_valid ph ->
  permheap_finite ph <->
  heap_finite (permheap_concr ph).
Proof.
  intros ph H1. split.
  (* left to right *)
  - intros (xs & FIN).
    exists xs. intros l H2. apply FIN.
    unfold permheap_concr, phc_concr in H2. desf.
  (* right to left *)
  - intros (xs & FIN).
    exists xs. intros l H2. apply FIN.
    unfold permheap_valid in H1.
    specialize H1 with l.
    unfold phc_valid in H1.
    unfold permheap_concr, phc_concr. desf.
Qed.


(** *** Heap cell conversion *)

(** This section discusses tools to convert the types of heap cells in permission heaps. *)

(** The operations [permheap_conv_std], [permheap_conv_proc], and [permheap_conv_act] are
    used to convert the heap cell at location [l] in a given permission heap [ph] to a _standard_,
    _process_, or _action_ heap cell, respectively. Later in this section we define
    similar operations that work on sequences of heap locations. *)

Definition permheap_conv_std (ph : PermHeap)(l : Loc) : PermHeap :=
  update ph l (phc_conv_std (ph l)).

Definition permheap_conv_proc (ph : PermHeap)(l : Loc) : PermHeap :=
  update ph l (phc_conv_proc (ph l)).

Definition permheap_conv_act (ph : PermHeap)(l : Loc) : PermHeap :=
  update ph l (phc_conv_act (ph l)).

Notation "'std' { ph ',' l }" := (permheap_conv_std ph l).
Notation "'proc' { ph ',' l }" := (permheap_conv_proc ph l).
Notation "'act' { ph ',' l }" := (permheap_conv_act ph l).

Lemma permheap_conv_std_idemp :
  forall ph l,
  permheap_conv_std (permheap_conv_std ph l) l =
  permheap_conv_std ph l.
Proof.
  intros ph l. extensionality l'.
  unfold permheap_conv_std, update. desf.
  by apply phc_conv_std_idemp.
Qed.

Lemma permheap_conv_proc_idemp :
  forall ph l,
  permheap_conv_proc (permheap_conv_proc ph l) l =
  permheap_conv_proc ph l.
Proof.
  intros ph l. extensionality l'.
  unfold permheap_conv_proc, update. desf.
  by apply phc_conv_proc_idemp.
Qed.

Lemma permheap_conv_act_idemp :
  forall ph l,
  permheap_conv_act (permheap_conv_act ph l) l =
  permheap_conv_act ph l.
Proof.
  intros ph l. extensionality l'.
  unfold permheap_conv_act, update. desf.
  by apply phc_conv_act_idemp.
Qed.

Lemma permheap_conv_std_valid :
  forall ph l,
  permheap_valid ph ->
  permheap_valid (permheap_conv_std ph l).
Proof.
  intros ph l H l'.
  unfold permheap_valid in *.
  specialize H with l'.
  unfold permheap_conv_std, update. desf.
  by apply phc_conv_std_valid.
Qed.

Lemma permheap_conv_proc_valid :
  forall ph l,
  permheap_valid ph ->
  permheap_valid (permheap_conv_proc ph l).
Proof.
  intros ph l H l'.
  unfold permheap_valid in *.
  specialize H with l'.
  unfold permheap_conv_proc, update. desf.
  by apply phc_conv_proc_valid.
Qed.

Lemma permheap_conv_act_valid :
  forall ph l,
  permheap_valid ph ->
  permheap_valid (permheap_conv_act ph l).
Proof.
  intros ph l H l'.
  unfold permheap_valid in *.
  specialize H with l'.
  unfold permheap_conv_act, update. desf.
  by apply phc_conv_act_valid.
Qed.

Lemma permheap_conv_std_disj :
  forall ph1 ph2 l,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_std ph1 l) (permheap_conv_std ph2 l).
Proof.
  intros ph1 ph2 l H1 l'.
  unfold permheap_disj in *.
  specialize H1 with l'.
  unfold permheap_conv_std, update. desf.
  by apply phc_conv_std_disj.
Qed.

Lemma permheap_conv_proc_disj :
  forall ph1 ph2 l,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_proc ph1 l) (permheap_conv_proc ph2 l).
Proof.
  intros ph1 ph2 l H1 l'.
  unfold permheap_disj in *.
  specialize H1 with l'.
  unfold permheap_conv_proc, update. desf.
  by apply phc_conv_proc_disj.
Qed.

Lemma permheap_conv_act_disj :
  forall ph1 ph2 l,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_act ph1 l) (permheap_conv_act ph2 l).
Proof.
  intros ph1 ph2 l H1 l'.
  unfold permheap_disj in *.
  specialize H1 with l'.
  unfold permheap_conv_act, update. desf.
  by apply phc_conv_act_disj.
Qed.

Lemma permheap_conv_std_full:
  forall ph l l',
  phc_full (permheap_conv_std ph l l') <->
  phc_full (ph l').
Proof.
  intros ph l l'. split; intro H.
  (* left to right *)
  - unfold permheap_conv_std, update in H. desf.
    by rewrite <- phc_conv_std_full.
  (* right to left *)
  - unfold permheap_conv_std, update. desf.
    by rewrite phc_conv_std_full.
Qed.

Lemma permheap_conv_proc_full:
  forall ph l l',
  phc_full (permheap_conv_proc ph l l') <->
  phc_full (ph l').
Proof.
  intros ph l l'. split; intro H.
  (* left to right *)
  - unfold permheap_conv_proc, update in H. desf.
    by rewrite <- phc_conv_proc_full.
  (* right to left *)
  - unfold permheap_conv_proc, update. desf.
    by rewrite phc_conv_proc_full.
Qed.

Lemma permheap_conv_act_full:
  forall ph l l',
  phc_full (permheap_conv_act ph l l') <->
  phc_full (ph l').
Proof.
  intros ph l l'. split; intro H.
  (* left to right *)
  - unfold permheap_conv_act, update in H. desf.
    by rewrite <- phc_conv_act_full.
  (* right to left *)
  - unfold permheap_conv_act, update. desf.
    by rewrite phc_conv_act_full.
Qed.

Lemma permheap_conv_std_disj_full :
  forall ph1 ph2 l,
  phc_full (ph1 l) ->
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_std ph1 l) ph2.
Proof.
  intros ph1 ph2 l H1 H2 l'.
  unfold permheap_conv_std, update.
  desf. by apply phc_conv_std_disj_full.
Qed.

Lemma permheap_conv_proc_disj_full :
  forall ph1 ph2 l,
  phc_full (ph1 l) ->
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_proc ph1 l) ph2.
Proof.
  intros ph1 ph2 l H1 H2 l'.
  unfold permheap_conv_proc, update.
  desf. by apply phc_conv_proc_disj_full.
Qed.

Lemma permheap_conv_act_disj_full :
  forall ph1 ph2 l,
  phc_full (ph1 l) ->
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_act ph1 l) ph2.
Proof.
  intros ph1 ph2 l H1 H2 l'.
  unfold permheap_conv_act, update.
  desf. by apply phc_conv_act_disj_full.
Qed.

Lemma permheap_conv_std_free :
  forall ph l,
  ph l = PHCfree ->
  permheap_conv_std ph l = ph.
Proof.
  intros ph l H. extensionality l'.
  unfold permheap_conv_std, update. desf.
  by apply phc_conv_std_free.
Qed.

Lemma permheap_conv_proc_free :
  forall ph l,
  ph l = PHCfree ->
  permheap_conv_proc ph l = ph.
Proof.
  intros ph l H. extensionality l'.
  unfold permheap_conv_proc, update. desf.
  by apply phc_conv_proc_free.
Qed.

Lemma permheap_conv_act_free :
  forall ph l,
  ph l = PHCfree ->
  permheap_conv_act ph l = ph.
Proof.
  intros ph l H. extensionality l'.
  unfold permheap_conv_act, update. desf.
  by apply phc_conv_act_free.
Qed.

Lemma permheap_conv_std_free2 :
  forall ph l l',
  (permheap_conv_std ph l) l' = PHCfree <-> ph l' = PHCfree.
Proof.
  intros ph l l'.
  unfold permheap_conv_std, update. desf.
  by apply phc_conv_std_free2.
Qed.

Lemma permheap_conv_proc_free2 :
  forall ph l l',
  (permheap_conv_proc ph l) l' = PHCfree <-> ph l' = PHCfree.
Proof.
  intros ph l l'.
  unfold permheap_conv_proc, update. desf.
  by apply phc_conv_proc_free2.
Qed.

Lemma permheap_conv_act_free2 :
  forall ph l l',
  (permheap_conv_act ph l) l' = PHCfree <-> ph l' = PHCfree.
Proof.
  intros ph l l'.
  unfold permheap_conv_act, update. desf.
  by apply phc_conv_act_free2.
Qed.

Lemma permheap_conv_std_add :
  forall ph1 ph2 l,
  permheap_disj ph1 ph2 ->
  permheap_conv_std (permheap_add ph1 ph2) l =
  permheap_add (permheap_conv_std ph1 l) (permheap_conv_std ph2 l).
Proof.
  intros ph1 ph2 l H1.
  extensionality l'.
  unfold permheap_disj in H1.
  specialize H1 with l'.
  unfold permheap_add, permheap_conv_std, update. desf.
  by apply phc_conv_std_add.
Qed.

Lemma permheap_conv_proc_add :
  forall ph1 ph2 l,
  permheap_disj ph1 ph2 ->
  permheap_conv_proc (permheap_add ph1 ph2) l =
  permheap_add (permheap_conv_proc ph1 l) (permheap_conv_proc ph2 l).
Proof.
  intros ph1 ph2 l H1.
  extensionality l'.
  unfold permheap_disj in H1.
  specialize H1 with l'.
  unfold permheap_add, permheap_conv_proc, update. desf.
  by apply phc_conv_proc_add.
Qed.

Lemma permheap_conv_act_add :
  forall ph1 ph2 l,
  permheap_disj ph1 ph2 ->
  permheap_conv_act (permheap_add ph1 ph2) l =
  permheap_add (permheap_conv_act ph1 l) (permheap_conv_act ph2 l).
Proof.
  intros ph1 ph2 l H1.
  extensionality l'.
  unfold permheap_disj in H1.
  specialize H1 with l'.
  unfold permheap_add, permheap_conv_act, update. desf.
  by apply phc_conv_act_add.
Qed.

Lemma permheap_conv_std_concr :
  forall ph l,
  permheap_concr (permheap_conv_std ph l) =
  permheap_concr ph.
Proof.
  intros ph l. extensionality l'.
  unfold permheap_concr, permheap_conv_std, update. desf.
  by rewrite phc_conv_std_concr.
Qed.

Lemma permheap_conv_proc_concr :
  forall ph l,
  permheap_concr (permheap_conv_proc ph l) =
  permheap_concr ph.
Proof.
  intros ph l. extensionality l'.
  unfold permheap_concr, permheap_conv_proc, update. desf.
  by rewrite phc_conv_proc_concr.
Qed.

Lemma permheap_conv_act_concr :
  forall ph l,
  permheap_concr (permheap_conv_act ph l) =
  permheap_concr ph.
Proof.
  intros ph l. extensionality l'.
  unfold permheap_concr, permheap_conv_act, update. desf.
  by rewrite phc_conv_act_concr.
Qed.

Lemma permheap_conv_std_pres :
  forall ph l l',
  l <> l' ->
  ph l' = permheap_conv_std ph l l'.
Proof.
  intros ph l l' H1.
  unfold permheap_conv_std, update. desf.
Qed.

Lemma permheap_conv_proc_pres :
  forall ph l l',
  l <> l' ->
  ph l' = permheap_conv_proc ph l l'.
Proof.
  intros ph l l' H1.
  unfold permheap_conv_proc, update. desf.
Qed.

Lemma permheap_conv_act_pres :
  forall ph l l',
  l <> l' ->
  ph l' = permheap_conv_act ph l l'.
Proof.
  intros ph l l' H1.
  unfold permheap_conv_act, update. desf.
Qed.

Lemma permheap_conv_std_apply :
  forall ph l,
  permheap_conv_std ph l l = phc_conv_std (ph l).
Proof.
  intros ph l. unfold permheap_conv_std, update. desf.
Qed.

Lemma permheap_conv_proc_apply :
  forall ph l,
  permheap_conv_proc ph l l = phc_conv_proc (ph l).
Proof.
  intros ph l. unfold permheap_conv_proc, update. desf.
Qed.

Lemma permheap_conv_act_apply :
  forall ph l,
  permheap_conv_act ph l l = phc_conv_act (ph l).
Proof.
  intros ph l. unfold permheap_conv_act, update. desf.
Qed.

Lemma permheap_snapshot_conv_proc_occ :
  forall ph l l',
  permheap_snapshot ph l' <> None ->
  permheap_snapshot (permheap_conv_proc ph l) l' <> None.
Proof.
  intros ph l l' H. unfold permheap_snapshot in *.
  unfold permheap_conv_proc, update. desf.
  by apply phc_snapshot_conv_proc_occ.
Qed.

Lemma permheap_snapshot_conv_act_occ :
  forall ph l l',
  permheap_snapshot ph l' <> None ->
  permheap_snapshot (permheap_conv_act ph l) l' <> None.
Proof.
  intros ph l l' H. unfold permheap_snapshot in *.
  unfold permheap_conv_act, update. desf.
  by apply phc_snapshot_conv_act_occ.
Qed.

Lemma permheap_snapshot_conv_act_pres :
  forall ph l l' v,
  permheap_snapshot ph l' = Some v ->
  permheap_snapshot (permheap_conv_act ph l) l' = Some v.
Proof.
  intros ph l l' v H1. unfold permheap_snapshot in *.
  unfold permheap_conv_act, update. desf.
  by apply phc_snapshot_conv_act_pres.
Qed.


(** The following three operations are used to convert the heap cell types of 
    a sequence [xs] of heap locations in a given permission heap [ph]. These
    operations build on the operations defined earlier in this section. *)

Fixpoint permheap_conv_std_mult (ph : PermHeap)(xs : list Loc) : PermHeap :=
  match xs with
    | nil => ph
    | l :: xs' => permheap_conv_std (permheap_conv_std_mult ph xs') l
  end.

Fixpoint permheap_conv_proc_mult (ph : PermHeap)(xs : list Loc) : PermHeap :=
  match xs with
    | nil => ph
    | l :: xs' => permheap_conv_proc (permheap_conv_proc_mult ph xs') l
  end.

Fixpoint permheap_conv_act_mult (ph : PermHeap)(xs : list Loc) : PermHeap :=
  match xs with
    | nil => ph
    | l :: xs' => permheap_conv_act (permheap_conv_act_mult ph xs') l
  end.

Notation "'std' { ph ';' xs }" := (permheap_conv_std_mult ph xs).
Notation "'proc' { ph ';' xs }" := (permheap_conv_proc_mult ph xs).
Notation "'act' { ph ';' xs }" := (permheap_conv_act_mult ph xs).

Lemma permheap_conv_std_nil :
  forall ph,
  ph = permheap_conv_std_mult ph nil.
Proof.
  ins.
Qed.

Lemma permheap_conv_proc_nil :
  forall ph,
  ph = permheap_conv_proc_mult ph nil.
Proof.
  ins.
Qed.

Lemma permheap_conv_act_nil :
  forall ph,
  ph = permheap_conv_act_mult ph nil.
Proof.
  ins.
Qed.

Lemma permheap_conv_std_single :
  forall ph l,
  permheap_conv_std ph l =
  permheap_conv_std_mult ph [l].
Proof.
  ins.
Qed.

Lemma permheap_conv_proc_single :
  forall ph l,
  permheap_conv_proc ph l =
  permheap_conv_proc_mult ph [l].
Proof.
  ins.
Qed.

Lemma permheap_conv_act_single :
  forall ph l,
  permheap_conv_act ph l =
  permheap_conv_act_mult ph [l].
Proof.
  ins.
Qed.

Lemma permheap_conv_std_mult_cons :
  forall (xs : list Loc)(l : Loc) ph,
  permheap_conv_std_mult ph (l :: xs) =
  permheap_conv_std (permheap_conv_std_mult ph xs) l.
Proof.
  ins.
Qed.

Lemma permheap_conv_proc_mult_cons :
  forall (xs : list Loc)(l : Loc) ph,
  permheap_conv_proc_mult ph (l :: xs) =
  permheap_conv_proc (permheap_conv_proc_mult ph xs) l.
Proof.
  ins.
Qed.

Lemma permheap_conv_act_mult_cons :
  forall (xs : list Loc)(l : Loc) ph,
  permheap_conv_act_mult ph (l :: xs) =
  permheap_conv_act (permheap_conv_act_mult ph xs) l.
Proof.
  ins.
Qed.

Lemma permheap_conv_std_mult_app :
  forall xs ys ph,
  permheap_conv_std_mult ph (xs ++ ys) =
  permheap_conv_std_mult (permheap_conv_std_mult ph ys) xs.
Proof.
  induction xs as [|l xs]. vauto.
  intros ys ph. simpls.
  by rewrite IHxs.
Qed.

Lemma permheap_conv_proc_mult_app :
  forall xs ys ph,
  permheap_conv_proc_mult ph (xs ++ ys) =
  permheap_conv_proc_mult (permheap_conv_proc_mult ph ys) xs.
Proof.
  induction xs as [|l xs]. vauto.
  intros ys ph. simpls.
  by rewrite IHxs.
Qed.

Lemma permheap_conv_act_mult_app :
  forall xs ys ph,
  permheap_conv_act_mult ph (xs ++ ys) =
  permheap_conv_act_mult (permheap_conv_act_mult ph ys) xs.
Proof.
  induction xs as [|l xs]. vauto.
  intros ys ph. simpls.
  by rewrite IHxs.
Qed.

Lemma permheap_conv_std_mult_permut :
  forall ph xs ys,
  Permutation xs ys ->
  permheap_conv_std_mult ph xs = permheap_conv_std_mult ph ys.
Proof.
  intros ph xs ys H. induction H; vauto.
  - simpl. by rewrite IHPermutation.
  - simpls. unfold permheap_conv_std, update.
    extensionality l'. desf.
  - by rewrite IHPermutation1, IHPermutation2.
Qed.

Add Parametric Morphism : permheap_conv_std_mult
  with signature eq ==> @Permutation Loc ==> eq
    as permheap_conv_std_mult_permut_mor.
Proof.
  intros ph xs ys H1.
  by apply permheap_conv_std_mult_permut.
Qed.

Lemma permheap_conv_proc_mult_permut :
  forall ph xs ys,
  Permutation xs ys ->
  permheap_conv_proc_mult ph xs = permheap_conv_proc_mult ph ys.
Proof.
  intros ph xs ys H. induction H; vauto.
  - simpl. by rewrite IHPermutation.
  - simpls. unfold permheap_conv_proc, update.
    extensionality l'. desf.
  - by rewrite IHPermutation1, IHPermutation2.
Qed.

Add Parametric Morphism : permheap_conv_proc_mult
  with signature eq ==> @Permutation Loc ==> eq
    as permheap_conv_proc_mult_permut_mor.
Proof.
  intros ph xs ys H1.
  by apply permheap_conv_proc_mult_permut.
Qed.

Lemma permheap_conv_act_mult_permut :
  forall ph xs ys,
  Permutation xs ys ->
  permheap_conv_act_mult ph xs = permheap_conv_act_mult ph ys.
Proof.
  intros ph xs ys H. induction H; vauto.
  - simpl. by rewrite IHPermutation.
  - simpls. unfold permheap_conv_act, update.
    extensionality l'. desf.
  - by rewrite IHPermutation1, IHPermutation2.
Qed.

Add Parametric Morphism : permheap_conv_act_mult
  with signature eq ==> @Permutation Loc ==> eq
    as permheap_conv_act_mult_permut_mor.
Proof.
  intros ph xs ys H1.
  by apply permheap_conv_act_mult_permut.
Qed.

Lemma permheap_conv_std_mult_idemp :
  forall (xs : list Loc) ph,
  permheap_conv_std_mult (permheap_conv_std_mult ph xs) xs =
  permheap_conv_std_mult ph xs.
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros ph. rewrite <- permheap_conv_std_mult_app.
  assert (H1 : Permutation ((l' :: xs) ++ l' :: xs) (l' :: l' :: xs ++ xs)). { list_permutation. }
  rewrite H1. simpl. rewrite permheap_conv_std_idemp.
  by rewrite permheap_conv_std_mult_app, IH.
Qed.

Lemma permheap_conv_proc_mult_idemp :
  forall (xs : list Loc) ph,
  permheap_conv_proc_mult (permheap_conv_proc_mult ph xs) xs =
  permheap_conv_proc_mult ph xs.
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros ph. rewrite <- permheap_conv_proc_mult_app.
  assert (H1 : Permutation ((l' :: xs) ++ l' :: xs) (l' :: l' :: xs ++ xs)). { list_permutation. }
  rewrite H1. simpl. rewrite permheap_conv_proc_idemp.
  by rewrite permheap_conv_proc_mult_app, IH.
Qed.

Lemma permheap_conv_act_mult_idemp :
  forall (xs : list Loc) ph,
  permheap_conv_act_mult (permheap_conv_act_mult ph xs) xs =
  permheap_conv_act_mult ph xs.
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros ph. rewrite <- permheap_conv_act_mult_app.
  assert (H1 : Permutation ((l' :: xs) ++ l' :: xs) (l' :: l' :: xs ++ xs)). { list_permutation. }
  rewrite H1. simpl. rewrite permheap_conv_act_idemp.
  by rewrite permheap_conv_act_mult_app, IH.
Qed.

Lemma permheap_conv_std_mult_subsume :
  forall (xs : list Loc)(l : Loc) ph,
  In l xs ->
  permheap_conv_std_mult ph (l :: xs) =
  permheap_conv_std_mult ph xs.
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros l ph H1. simpl in H1. destruct H1 as [H1 | H1]; vauto.
  (* [l] is equal to [l'] *)
  - simpls. by rewrite permheap_conv_std_idemp.
  (* [l] is not equal to [l'] *)
  - rewrite perm_swap. simpls. rewrite IH; vauto.
Qed.

Lemma permheap_conv_proc_mult_subsume :
  forall (xs : list Loc)(l : Loc) ph,
  In l xs ->
  permheap_conv_proc_mult ph (l :: xs) =
  permheap_conv_proc_mult ph xs.
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros l ph H1. simpl in H1. destruct H1 as [H1 | H1]; vauto.
  (* [l] is equal to [l'] *)
  - simpls. by rewrite permheap_conv_proc_idemp.
  (* [l] is not equal to [l'] *)
  - rewrite perm_swap. simpls. rewrite IH; vauto.
Qed.

Lemma permheap_conv_act_mult_subsume :
  forall (xs : list Loc)(l : Loc) ph,
  In l xs ->
  permheap_conv_act_mult ph (l :: xs) =
  permheap_conv_act_mult ph xs.
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros l ph H1. simpl in H1. destruct H1 as [H1 | H1]; vauto.
  (* [l] is equal to [l'] *)
  - simpls. by rewrite permheap_conv_act_idemp.
  (* [l] is not equal to [l'] *)
  - rewrite perm_swap. simpls. rewrite IH; vauto.
Qed.

Lemma permheap_conv_std_mult_valid :
  forall xs ph,
  permheap_valid ph ->
  permheap_valid (permheap_conv_std_mult ph xs).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph H. simpl.
  by apply permheap_conv_std_valid, IH.
Qed.

Lemma permheap_conv_proc_mult_valid :
  forall xs ph,
  permheap_valid ph ->
  permheap_valid (permheap_conv_proc_mult ph xs).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph H. simpl.
  by apply permheap_conv_proc_valid, IH.
Qed.

Lemma permheap_conv_act_mult_valid :
  forall xs ph,
  permheap_valid ph ->
  permheap_valid (permheap_conv_act_mult ph xs).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph H. simpl.
  by apply permheap_conv_act_valid, IH.
Qed.

Lemma permheap_conv_std_mult_free :
  forall (xs : list Loc) ph,
    (forall l : Loc, In l xs -> ph l = PHCfree) ->
  permheap_conv_std_mult ph xs = ph.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph H1. simpl.
  rewrite permheap_conv_std_free.
  - apply IH. intros l' H2.
    apply H1. by apply in_cons.
  - rewrite IH.
    + apply H1. vauto.
    + intros l' H2. by apply H1, in_cons.
Qed.

Lemma permheap_conv_proc_mult_free :
  forall (xs : list Loc) ph,
    (forall l : Loc, In l xs -> ph l = PHCfree) ->
  permheap_conv_proc_mult ph xs = ph.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph H1. simpl.
  rewrite permheap_conv_proc_free.
  - apply IH. intros l' H2.
    apply H1. by apply in_cons.
  - rewrite IH.
    + apply H1. vauto.
    + intros l' H2. by apply H1, in_cons.
Qed.

Lemma permheap_conv_act_mult_free :
  forall (xs : list Loc) ph,
    (forall l : Loc, In l xs -> ph l = PHCfree) ->
  permheap_conv_act_mult ph xs = ph.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph H1. simpl.
  rewrite permheap_conv_act_free.
  - apply IH. intros l' H2.
    apply H1. by apply in_cons.
  - rewrite IH.
    + apply H1. vauto.
    + intros l' H2. by apply H1, in_cons.
Qed.

Lemma permheap_conv_std_mult_free2 :
  forall (xs : list Loc) ph l,
  permheap_conv_std_mult ph xs l = PHCfree <-> ph l = PHCfree.
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros ph l. simpl.
  rewrite permheap_conv_std_free2.
  by rewrite IH.
Qed.

Lemma permheap_conv_proc_mult_free2 :
  forall (xs : list Loc) ph l,
  permheap_conv_proc_mult ph xs l = PHCfree <-> ph l = PHCfree.
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros ph l. simpl.
  rewrite permheap_conv_proc_free2.
  by rewrite IH.
Qed.

Lemma permheap_conv_act_mult_free2 :
  forall (xs : list Loc) ph l,
  permheap_conv_act_mult ph xs l = PHCfree <-> ph l = PHCfree.
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros ph l. simpl.
  rewrite permheap_conv_act_free2.
  by rewrite IH.
Qed.

Lemma permheap_conv_std_mult_disj :
  forall xs ph1 ph2,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_std_mult ph1 xs) (permheap_conv_std_mult ph2 xs).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph1 ph2 H1. simpl.
  apply permheap_conv_std_disj.
  by apply IH.
Qed.

Lemma permheap_conv_proc_mult_disj :
  forall xs ph1 ph2,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_proc_mult ph1 xs) (permheap_conv_proc_mult ph2 xs).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph1 ph2 H1. simpl.
  apply permheap_conv_proc_disj.
  by apply IH.
Qed.

Lemma permheap_conv_act_mult_disj :
  forall xs ph1 ph2,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_act_mult ph1 xs) (permheap_conv_act_mult ph2 xs).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph1 ph2 H1. simpl.
  apply permheap_conv_act_disj.
  by apply IH.
Qed.

Lemma permheap_conv_std_mult_full:
  forall xs ph l,
  phc_full (permheap_conv_std_mult ph xs l) <->
  phc_full (ph l).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph l'. split; intro H.
  (* left to right *)
  - simpl in H. rewrite <- IH.
    by rewrite <- permheap_conv_std_full with (l := l).
  (* right to left *)
  - simpl. rewrite permheap_conv_std_full with (l := l).
    by rewrite IH.
Qed.

Lemma permheap_conv_proc_mult_full:
  forall xs ph l,
  phc_full (permheap_conv_proc_mult ph xs l) <->
  phc_full (ph l).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph l'. split; intro H.
  (* left to right *)
  - simpl in H. rewrite <- IH.
    by rewrite <- permheap_conv_proc_full with (l := l).
  (* right to left *)
  - simpl. rewrite permheap_conv_proc_full with (l := l).
    by rewrite IH.
Qed.

Lemma permheap_conv_act_mult_full:
  forall xs ph l,
  phc_full (permheap_conv_act_mult ph xs l) <->
  phc_full (ph l).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph l'. split; intro H.
  (* left to right *)
  - simpl in H. rewrite <- IH.
    by rewrite <- permheap_conv_act_full with (l := l).
  (* right to left *)
  - simpl. rewrite permheap_conv_act_full with (l := l).
    by rewrite IH.
Qed.

Lemma permheap_conv_std_mult_disj_full :
  forall xs ph1 ph2,
    (forall l, In l xs -> phc_full (ph1 l)) ->
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_std_mult ph1 xs) ph2.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph1 ph2 H1 H2. simpl.
  apply permheap_conv_std_disj_full.
  - rewrite permheap_conv_std_mult_full.
    apply H1. vauto.
  - apply IH; auto. intros l' H3.
    apply H1. vauto.
Qed.

Lemma permheap_conv_proc_mult_disj_full :
  forall xs ph1 ph2,
    (forall l, In l xs -> phc_full (ph1 l)) ->
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_proc_mult ph1 xs) ph2.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph1 ph2 H1 H2. simpl.
  apply permheap_conv_proc_disj_full.
  - rewrite permheap_conv_proc_mult_full.
    apply H1. vauto.
  - apply IH; auto. intros l' H3.
    apply H1. vauto.
Qed.

Lemma permheap_conv_act_mult_disj_full :
  forall xs ph1 ph2,
    (forall l, In l xs -> phc_full (ph1 l)) ->
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_conv_act_mult ph1 xs) ph2.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph1 ph2 H1 H2. simpl.
  apply permheap_conv_act_disj_full.
  - rewrite permheap_conv_act_mult_full.
    apply H1. vauto.
  - apply IH; auto. intros l' H3.
    apply H1. vauto.
Qed.

Lemma permheap_conv_std_mult_add :
  forall (xs : list Loc) ph1 ph2,
  permheap_disj ph1 ph2 ->
  permheap_conv_std_mult (permheap_add ph1 ph2) xs =
  permheap_add (permheap_conv_std_mult ph1 xs) (permheap_conv_std_mult ph2 xs).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph1 ph2 H1. simpl.
  rewrite <- permheap_conv_std_add.
  - by rewrite <- IH.
  - by apply permheap_conv_std_mult_disj.
Qed.

Lemma permheap_conv_proc_mult_add :
  forall (xs : list Loc) ph1 ph2,
  permheap_disj ph1 ph2 ->
  permheap_conv_proc_mult (permheap_add ph1 ph2) xs =
  permheap_add (permheap_conv_proc_mult ph1 xs) (permheap_conv_proc_mult ph2 xs).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph1 ph2 H1. simpl.
  rewrite <- permheap_conv_proc_add.
  - by rewrite <- IH.
  - by apply permheap_conv_proc_mult_disj.
Qed.

Lemma permheap_conv_act_mult_add :
  forall (xs : list Loc) ph1 ph2,
  permheap_disj ph1 ph2 ->
  permheap_conv_act_mult (permheap_add ph1 ph2) xs =
  permheap_add (permheap_conv_act_mult ph1 xs) (permheap_conv_act_mult ph2 xs).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph1 ph2 H1. simpl.
  rewrite <- permheap_conv_act_add.
  - by rewrite <- IH.
  - by apply permheap_conv_act_mult_disj.
Qed.

Lemma permheap_conv_std_mult_concr :
  forall (xs : list Loc) ph,
  permheap_concr (permheap_conv_std_mult ph xs) =
  permheap_concr ph.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph. simpl.
  by rewrite permheap_conv_std_concr, IH.
Qed.

Lemma permheap_conv_proc_mult_concr :
  forall (xs : list Loc) ph,
  permheap_concr (permheap_conv_proc_mult ph xs) =
  permheap_concr ph.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph. simpl.
  by rewrite permheap_conv_proc_concr, IH.
Qed.

Lemma permheap_conv_act_mult_concr :
  forall (xs : list Loc) ph,
  permheap_concr (permheap_conv_act_mult ph xs) =
  permheap_concr ph.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros ph. simpl.
  by rewrite permheap_conv_act_concr, IH.
Qed.

Lemma permheap_conv_std_mult_pres :
  forall (xs : list Loc)(l : Loc) ph,
  ~ In l xs ->
  ph l = permheap_conv_std_mult ph xs l.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros l' ph H1. simpl. rewrite IH.
  - apply permheap_conv_std_pres. intro H2.
    apply H1. clarify. simpl. by left.
  - intro H2. apply H1. simpl. by right.
Qed.

Lemma permheap_conv_proc_mult_pres :
  forall (xs : list Loc)(l : Loc) ph,
  ~ In l xs ->
  ph l = permheap_conv_proc_mult ph xs l.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros l' ph H1. simpl. rewrite IH.
  - apply permheap_conv_proc_pres. intro H2.
    apply H1. clarify. simpl. by left.
  - intro H2. apply H1. simpl. by right.
Qed.

Lemma permheap_conv_act_mult_pres :
  forall (xs : list Loc)(l : Loc) ph,
  ~ In l xs ->
  ph l = permheap_conv_act_mult ph xs l.
Proof.
  induction xs as [|l xs IH]. vauto.
  intros l' ph H1. simpl. rewrite IH.
  - apply permheap_conv_act_pres. intro H2.
    apply H1. clarify. simpl. by left.
  - intro H2. apply H1. simpl. by right.
Qed.

Lemma permheap_conv_std_mult_apply :
  forall (xs : list Loc)(l : Loc) ph,
  In l xs ->
  permheap_conv_std_mult ph xs l = phc_conv_std (ph l).
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros l ph H1. simpl in H1. destruct H1 as [H1 | H1]; vauto.
  (* [l] is equal to [l'] *)
  - simpl. rewrite permheap_conv_std_apply.
    assert (H2 : In l xs \/ ~ In l xs). { by apply classic. }
    destruct H2 as [H2 | H2]; vauto.
    + rewrite IH; auto. by rewrite phc_conv_std_idemp.
    + by rewrite <- permheap_conv_std_mult_pres.
  (* [l] is not equal to [l'] *)
  - simpl. unfold permheap_conv_std, update. desf.
    + rewrite IH; auto. by apply phc_conv_std_idemp.
    + by apply IH.
Qed.

Lemma permheap_conv_proc_mult_apply :
  forall (xs : list Loc)(l : Loc) ph,
  In l xs ->
  permheap_conv_proc_mult ph xs l = phc_conv_proc (ph l).
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros l ph H1. simpl in H1. destruct H1 as [H1 | H1]; vauto.
  (* [l] is equal to [l'] *)
  - simpl. rewrite permheap_conv_proc_apply.
    assert (H2 : In l xs \/ ~ In l xs). { by apply classic. }
    destruct H2 as [H2 | H2]; vauto.
    + rewrite IH; auto. by rewrite phc_conv_proc_idemp.
    + by rewrite <- permheap_conv_proc_mult_pres.
  (* [l] is not equal to [l'] *)
  - simpl. unfold permheap_conv_proc, update. desf.
    + rewrite IH; auto. by apply phc_conv_proc_idemp.
    + by apply IH.
Qed.

Lemma permheap_conv_act_mult_apply :
  forall (xs : list Loc)(l : Loc) ph,
  In l xs ->
  permheap_conv_act_mult ph xs l = phc_conv_act (ph l).
Proof.
  induction xs as [|l' xs IH]. vauto.
  intros l ph H1. simpl in H1. destruct H1 as [H1 | H1]; vauto.
  (* [l] is equal to [l'] *)
  - simpl. rewrite permheap_conv_act_apply.
    assert (H2 : In l xs \/ ~ In l xs). { by apply classic. }
    destruct H2 as [H2 | H2]; vauto.
    + rewrite IH; auto. by rewrite phc_conv_act_idemp.
    + by rewrite <- permheap_conv_act_mult_pres.
  (* [l] is not equal to [l'] *)
  - simpl. unfold permheap_conv_act, update. desf.
    + rewrite IH; auto. by apply phc_conv_act_idemp.
    + by apply IH.
Qed.

Lemma permheap_snapshot_conv_proc_mult_occ :
  forall (ls : list Loc) ph l,
  permheap_snapshot ph l <> None ->
  permheap_snapshot (permheap_conv_proc_mult ph ls) l <> None.
Proof.
  induction ls as [|l ls IH]. vauto.
  intros ph l' H1. simpls.
  by apply permheap_snapshot_conv_proc_occ, IH.
Qed.

Lemma permheap_snapshot_conv_act_mult_occ :
  forall (ls : list Loc) ph l,
  permheap_snapshot ph l <> None ->
  permheap_snapshot (permheap_conv_act_mult ph ls) l <> None.
Proof.
  induction ls as [|l ls IH]. vauto.
  intros ph l' H1. simpls.
  by apply permheap_snapshot_conv_act_occ, IH.
Qed.

Lemma permheap_snapshot_conv_act_mult_pres :
  forall (ls : list Loc) ph l v,
  permheap_snapshot ph l = Some v ->
  permheap_snapshot (permheap_conv_act_mult ph ls) l = Some v.
Proof.
  induction ls as [|l ls IH]. vauto.
  intros ph l' v H1. simpls.
  by apply permheap_snapshot_conv_act_pres, IH.
Qed.
