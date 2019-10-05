Require Import FunctionalExtensionality.
Require Import HahnBase.
Require Import Heap.
Require Import List.
Require Import Permissions.
Require Import Permutation.
Require Import PermutationTactic.
Require Import Prerequisites.
Require Import Process.
Require Import QArith.
Require Import Qcanon.
Require Import Statics.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.


(** * Process Maps *)

(** ** Process map values *)

(** The set [ProcMapVal] of _process map values_ is used as the
    codomain for process maps. *)

Inductive ProcMapVal :=
  | PMelem(q:Qc)(p:ProcLabel)(P:Proc)(xs:list ProcVar)(f:ProcVar->Loc)
  | PMfree
  | PMinvalid.

Add Search Blacklist "ProcMapVal_rect".
Add Search Blacklist "ProcMapVal_ind".
Add Search Blacklist "ProcMapVal_rec".


(** *** Equality (up to bisimulation) *)

(** Two process map values are _equal_ (up to bisimulation) if their components all agree,
    and their process terms are bisimilar. *)

Definition pmv_eq (pmv1 pmv2 : ProcMapVal) : Prop :=
  match pmv1, pmv2 with
    | PMelem q1 p1 P1 xs1 f1, PMelem q2 p2 P2 xs2 f2 =>
        q1 = q2 /\ p1 = p2 /\ proc_bisim P1 P2 /\ xs1 = xs2 /\ map f1 xs1 = map f2 xs2
    | PMfree, PMfree
    | PMinvalid, PMinvalid => True
    | _, _ => False
  end.

Notation "A ≈ B" := (pmv_eq A B) (only printing, at level 80).

Instance pmv_eq_refl :
  Reflexive pmv_eq.
Proof.
  intro. red. desf.
Qed.

Hint Resolve pmv_eq_refl.

Instance pmv_eq_symm :
  Symmetric pmv_eq.
Proof.
  unfold pmv_eq. red. ins. desf. intuition.
Qed.

Hint Resolve pmv_eq_symm.

Instance pmv_eq_trans :
  Transitive pmv_eq.
Proof.
  unfold pmv_eq.
  red. ins. desf. intuition clarify.
  by transitivity P1. congruence.
Qed.

Instance pmv_eq_equiv :
  Equivalence pmv_eq.
Proof.
  split; intuition.
Qed.

Lemma pmv_eq_free :
  forall pmv1 pmv2,
  pmv_eq pmv1 pmv2 -> pmv1 = PMfree -> pmv2 = PMfree.
Proof.
  intros pmv1 pmv2 H1 H2.
  unfold pmv_eq in H1. desf.
Qed.

Add Parametric Morphism : PMelem
  with signature eq ==> eq ==> proc_bisim ==> eq ==> eq ==> pmv_eq
    as PMelem_bisim_mor.
Proof.
  intros q p P1 P2 H1 f.
  unfold pmv_eq. intuition vauto.
Qed.

Lemma pmv_eq_equality :
  forall pmv q p P xs f,
  pmv_eq pmv (PMelem q p P xs f) ->
  exists P' f',
    pmv = PMelem q p P' xs f' /\
    pmv_eq (PMelem q p P xs f) (PMelem q p P' xs f').
Proof.
  intros [q' p' P' xs' f'| |] q p P xs f H1; vauto.
  exists P', f'. intuition vauto.
  - unfold pmv_eq in H1. repeat desf.
  - rewrite <- H1. unfold pmv_eq in *. repeat desf.
Qed.

Lemma pmv_eq_F :
  forall q p P xs F1 F2,
    (forall x : ProcVar, In x xs -> F1 x = F2 x) ->
  pmv_eq (PMelem q p P xs F1) (PMelem q p P xs F2).
Proof.
  intros q p P xs F1 F2 IN1. red. repeat split; vauto.
  by apply map_ext_in.
Qed.


(** *** Validity *)

(** A process map value is _valid_ if its permission component is valid. *)

Definition pmv_valid (pmv : ProcMapVal) : Prop :=
  match pmv with
    | PMelem q _ _ _ _ => perm_valid q
    | PMfree => True
    | PMinvalid => False
  end.

Notation "√ A" := (pmv_valid A) (only printing, at level 80).

Lemma pmv_valid_eq :
  forall pmv1 pmv2,
  pmv_eq pmv1 pmv2 -> pmv_valid pmv1 -> pmv_valid pmv2.
Proof.
  unfold pmv_eq, pmv_valid. ins. repeat desf.
Qed.

Add Parametric Morphism : pmv_valid
  with signature pmv_eq ==> iff
    as pmv_valid_mor.
Proof.
  ins. split; apply pmv_valid_eq; auto.
Qed.

Lemma pmv_valid_iden :
  pmv_valid PMfree.
Proof.
  ins.
Qed.

Hint Resolve pmv_valid_iden.


(** *** Disjointness *)

(** Two process map values are _disjoint_ if their permission components
    are together disjoint. *)

Definition pmv_disj (pmv1 pmv2 : ProcMapVal) : Prop :=
  match (pmv1, pmv2) with
    | (PMelem q1 p1 _ xs1 f1, PMelem q2 p2 _ xs2 f2) =>
        perm_disj q1 q2 /\ p1 = p2 /\ xs1 = xs2 /\ map f1 xs1 = map f2 xs2
    | (PMelem q _ _ _ _, PMfree)
    | (PMfree, PMelem q _ _ _ _) => perm_valid q
    | (PMfree, PMfree) => True
    | (PMinvalid, _)
    | (_, PMinvalid) => False
  end.

Notation "A ⟂ B" := (pmv_disj A B) (only printing, at level 80).

Instance pmv_disj_symm :
  Symmetric pmv_disj.
Proof.
  unfold pmv_disj. red. ins.
  desf. intuition.
Qed.

Hint Resolve pmv_disj_symm.

Lemma pmv_disj_iden_l :
  forall pmv,
  pmv_valid pmv -> pmv_disj pmv PMfree.
Proof.
  ins.
Qed.

Hint Resolve pmv_disj_iden_l.

Lemma pmv_disj_iden_r :
  forall pmv,
  pmv_valid pmv -> pmv_disj PMfree pmv.
Proof.
  ins.
Qed.

Hint Resolve pmv_disj_iden_r.

Lemma pmv_disj_valid_l :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 -> pmv_valid pmv1.
Proof.
  intros pmv1 pmv2 H.
  unfold pmv_disj, pmv_valid in *.
  desf. intuition vauto.
  by apply perm_disj_valid_l in H0.
Qed.

Lemma pmv_disj_valid_r :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 -> pmv_valid pmv2.
Proof.
  intros pmv1 pmv2 H. symmetry in H.
  by apply pmv_disj_valid_l with pmv1.
Qed.

Lemma pmv_disj_valid :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 -> pmv_valid pmv1 /\ pmv_valid pmv2.
Proof.
  intros pmv1 pmv2 H. split.
  by apply pmv_disj_valid_l with pmv2.
  by apply pmv_disj_valid_r with pmv1.
Qed.

Lemma pmv_disj_eq_l :
  forall pmv1 pmv2 pmv,
  pmv_eq pmv1 pmv2 -> pmv_disj pmv1 pmv -> pmv_disj pmv2 pmv.
Proof.
  unfold pmv_eq, pmv_disj.
  ins. repeat desf.
  intuition congruence.
Qed.

Lemma pmv_disj_eq_r :
  forall pmv1 pmv2 pmv,
  pmv_eq pmv1 pmv2 -> pmv_disj pmv pmv1 -> pmv_disj pmv pmv2.
Proof.
  unfold pmv_eq, pmv_disj.
  intros pmv1 pmv2 pmv H1 H2.
  simpls. repeat desf.
  intuition congruence.
Qed.

Add Parametric Morphism : pmv_disj
  with signature pmv_eq ==> pmv_eq ==> iff
    as pmv_disj_mor.
Proof.
  intros pmv1 pmv1' H1 pmv2 pmv2' H2.
  split; intro H.
  apply pmv_disj_eq_l with pmv1; auto.
  apply pmv_disj_eq_r with pmv2; auto.
  apply pmv_disj_eq_l with pmv1'; auto.
  apply pmv_disj_eq_r with pmv2'; auto.
Qed.

(** *** Addition *)

(** The addition of two process map values is defined as the addition of their process and permission components. *)

Definition pmv_add (pmv1 pmv2 : ProcMapVal) : ProcMapVal :=
  match pmv1, pmv2 with
    | PMelem q1 p1 P1 xs1 f1, PMelem q2 p2 P2 xs2 f2 =>
        if Z.eq_dec p1 p2 then
          if list_eq_dec Z.eq_dec xs1 xs2 then
            if list_eq_dec Z.eq_dec (map f1 xs1) (map f2 xs2)
            then PMelem (q1 + q2) p1 (Ppar P1 P2) xs1 f1
            else PMinvalid
          else PMinvalid
        else PMinvalid
    | PMelem q p P xs f, PMfree
    | PMfree, PMelem q p P xs f => PMelem q p P xs f
    | PMfree, PMfree => PMfree
    | PMinvalid, _
    | _, PMinvalid => PMinvalid
  end.

Notation "A ⊕ B" := (pmv_add A B) (only printing, at level 80, right associativity).

Lemma pmv_add_assoc :
  forall pmv1 pmv2 pmv3,
  pmv_eq (pmv_add (pmv_add pmv1 pmv2) pmv3) (pmv_add pmv1 (pmv_add pmv2 pmv3)).
Proof.
  unfold pmv_add. ins.
  desf; try congruence.
  unfold pmv_eq. intuition vauto.
  by rewrite Qcplus_assoc.
  by rewrite proc_M2.
Qed.

Lemma pmv_add_comm :
  forall pmv1 pmv2,
  pmv_eq (pmv_add pmv1 pmv2) (pmv_add pmv2 pmv1).
Proof.
  unfold pmv_add. ins.
  repeat desf; try congruence.
  unfold pmv_eq. intuition.
  apply Qcplus_comm.
  rewrite proc_M1. auto.
Qed.

Hint Resolve pmv_add_comm.

Lemma pmv_add_valid :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 -> pmv_valid (pmv_add pmv1 pmv2).
Proof.
  unfold pmv_disj, pmv_add, pmv_valid.
  ins. repeat desf.
  by apply perm_add_valid.
Qed.

Lemma pmv_add_iden_l :
  forall pmv, pmv_add pmv PMfree = pmv.
Proof.
  unfold pmv_add. ins. desf.
Qed.

Hint Rewrite pmv_add_iden_l.

Lemma pmv_add_iden_r :
  forall pmv, pmv_add PMfree pmv = pmv.
Proof.
  unfold pmv_add. ins. desf.
Qed.

Hint Rewrite pmv_add_iden_r.

Lemma pmv_add_eq_l :
  forall pmv1 pmv2 pmv,
  pmv_eq pmv1 pmv2 ->
  pmv_eq (pmv_add pmv1 pmv) (pmv_add pmv2 pmv).
Proof.
  unfold pmv_eq, pmv_add. ins.
  repeat desf; intuition try congruence.
  by rewrite H1.
Qed.

Lemma pmv_add_eq_r :
  forall pmv1 pmv2 pmv,
  pmv_eq pmv1 pmv2 ->
  pmv_eq (pmv_add pmv pmv1) (pmv_add pmv pmv2).
Proof.
  unfold pmv_eq, pmv_add. ins.
  repeat desf; intuition try congruence.
  by rewrite H1.
Qed.

Add Parametric Morphism : pmv_add
  with signature pmv_eq ==> pmv_eq ==> pmv_eq
    as pmv_add_mor.
Proof.
  intros pmv1 pmv1' H1 pmv2 pmv2' H2.
  transitivity (pmv_add pmv1' pmv2).
  by apply pmv_add_eq_l.
  by apply pmv_add_eq_r.
Qed.

Lemma pmv_add_elem :
  forall q1 q2 p P1 P2 xs f,
  pmv_add (PMelem q1 p P1 xs f) (PMelem q2 p P2 xs f) =
  PMelem (q1 + q2) p (Ppar P1 P2) xs f.
Proof.
  intros q1 q2 p P1 P2 xs f.
  unfold pmv_add. desf.
Qed.

Lemma pmv_disj_add_l :
  forall pmv1 pmv2 pmv3,
  pmv_disj pmv1 pmv2 ->
  pmv_disj (pmv_add pmv1 pmv2) pmv3 ->
  pmv_disj pmv2 pmv3.
Proof.
  unfold pmv_add, pmv_disj.
  intros pmv1 pmv2 pmv3 H1 H2.
  desf; intuition vauto; des.
  by apply perm_disj_add_l in H1.
  congruence.
  by apply perm_disj_valid_r in H.
  by apply perm_disj_valid_r in H.
Qed.

Lemma pmv_disj_add_r :
  forall pmv1 pmv2 pmv3,
  pmv_disj pmv2 pmv3 ->
  pmv_disj pmv1 (pmv_add pmv2 pmv3) ->
  pmv_disj pmv1 pmv2.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2.
  symmetry in H1, H2.
  rewrite pmv_add_comm in H2; auto.
  apply pmv_disj_add_l in H2; auto.
Qed.

Lemma pmv_disj_assoc_l :
  forall pmv1 pmv2 pmv3,
  pmv_disj pmv1 pmv2 ->
  pmv_disj (pmv_add pmv1 pmv2) pmv3 ->
  pmv_disj pmv1 (pmv_add pmv2 pmv3).
Proof.
  unfold pmv_disj, pmv_add.
  intros pmv1 pmv2 pmv3 H1 H2.
  desf; intuition vauto; desf.
  by apply perm_disj_assoc_l.
  congruence.
  by apply perm_add_valid.
Qed.

Lemma pmv_disj_assoc_r :
  forall pmv1 pmv2 pmv3,
  pmv_disj pmv2 pmv3 ->
  pmv_disj pmv1 (pmv_add pmv2 pmv3) ->
  pmv_disj (pmv_add pmv1 pmv2) pmv3.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2.
  symmetry in H1, H2.
  rewrite pmv_add_comm in H2; auto.
  apply pmv_disj_assoc_l in H2; auto.
  rewrite pmv_add_comm in H2; auto.
Qed.

Lemma pmv_disj_swap_r :
  forall pmv1 pmv2 pmv3,
  pmv_disj pmv1 pmv2 ->
  pmv_disj (pmv_add pmv1 pmv2) pmv3 ->
  pmv_disj (pmv_add pmv1 pmv3) pmv2.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2.
  assert (H3 : pmv_disj pmv2 pmv3). {
    by apply pmv_disj_add_l with pmv1. }
  rewrite pmv_add_comm.
  apply pmv_disj_assoc_r; auto.
Qed.

Lemma pmv_disj_swap_l :
  forall pmv1 pmv2 pmv3,
  pmv_disj pmv1 pmv2 ->
  pmv_disj (pmv_add pmv1 pmv2) pmv3 ->
  pmv_disj (pmv_add pmv2 pmv3) pmv1.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2.
  apply pmv_disj_swap_r; auto.
  by rewrite pmv_add_comm.
Qed.

Lemma pmv_disj_middle :
  forall pmv1 pmv2 pmv3 pmv4,
  pmv_disj pmv1 pmv2 ->
  pmv_disj pmv3 pmv4 ->
  pmv_disj (pmv_add pmv1 pmv2) (pmv_add pmv3 pmv4) ->
  pmv_disj pmv2 pmv3.
Proof.
  intros pmv1 pmv2 pmv3 pmv4 H1 H2 H3.
  apply pmv_disj_add_l with pmv1; auto.
  by apply pmv_disj_add_r with pmv4.
Qed.

Lemma pmv_disj_compat :
  forall pmv1 pmv2 pmv3 pmv4,
  pmv_disj pmv1 pmv3 ->
  pmv_disj pmv2 pmv4 ->
  pmv_disj (pmv_add pmv1 pmv3) (pmv_add pmv2 pmv4) ->
  pmv_disj (pmv_add pmv1 pmv2) (pmv_add pmv3 pmv4).
Proof.
  intros pmv1 pmv2 pmv3 pmv4 H1 H2 H3.
  apply pmv_disj_assoc_r.
  rewrite pmv_add_comm.
  apply pmv_disj_assoc_l; auto.
  symmetry. by apply pmv_disj_add_l in H3.
  rewrite pmv_add_comm.
  rewrite pmv_add_assoc.
  apply pmv_disj_assoc_l; auto.
  by rewrite pmv_add_comm with (pmv1:=pmv4)(pmv2:=pmv2).
Qed.

Lemma pmv_add_swap_l :
  forall pmv1 pmv2 pmv3,
  pmv_eq (pmv_add pmv1 (pmv_add pmv2 pmv3)) (pmv_add pmv2 (pmv_add pmv1 pmv3)).
Proof.
  ins. repeat rewrite <- pmv_add_assoc.
  by apply pmv_add_eq_l, pmv_add_comm.
Qed.

Lemma pmv_add_swap_r :
  forall pmv1 pmv2 pmv3,
  pmv_eq (pmv_add (pmv_add pmv1 pmv2) pmv3) (pmv_add (pmv_add pmv1 pmv3) pmv2).
Proof.
  ins. repeat rewrite pmv_add_assoc.
  by apply pmv_add_eq_r, pmv_add_comm.
Qed.

Lemma pmv_add_compat :
  forall pmv1 pmv2 pmv3 pmv4,
  pmv_eq (pmv_add (pmv_add pmv1 pmv3) (pmv_add pmv2 pmv4)) (pmv_add (pmv_add pmv1 pmv2) (pmv_add pmv3 pmv4)).
Proof.
  ins. repeat rewrite pmv_add_assoc.
  apply pmv_add_eq_r.
  repeat rewrite <- pmv_add_assoc.
  apply pmv_add_eq_l, pmv_add_comm.
Qed.

Lemma pmv_add_free :
  forall pmv1 pmv2,
  pmv_add pmv1 pmv2 = PMfree <->
  pmv1 = PMfree /\ pmv2 = PMfree.
Proof.
  intros pmv1 pmv2.
  unfold pmv_add.
  intuition desf.
Qed.

Lemma pmv_add_not_free :
  forall pmv1 pmv2,
  pmv_add pmv1 pmv2 <> PMfree <->
  pmv1 <> PMfree \/ pmv2 <> PMfree.
Proof.
  intros pmv1 pmv2. split; intro H.
  - unfold pmv_add in H. desf; vauto.
  - unfold pmv_add. desf; vauto.
Qed.


(** *** Entirety *)

(** The predicate [pmv_full] determines whether a given process map value
    is _full_ or not. The remaining of this section discusses several
    properties and results of [pmv_full]. *)

Definition pmv_full (pmv : ProcMapVal) : Prop :=
  match pmv with
    | PMfree
    | PMinvalid => False
    | PMelem q _ _ _ _ => q = perm_full
  end.

Lemma pmv_full_eq :
  forall pmv1 pmv2,
  pmv_eq pmv1 pmv2 ->
  pmv_full pmv1 ->
  pmv_full pmv2.
Proof.
  unfold pmv_eq, pmv_full.
  ins. repeat desf.
Qed.

Add Parametric Morphism : pmv_full
  with signature pmv_eq ==> iff
    as pmv_full_mor.
Proof.
  intros pmv1 pmv2 H1. split; intro H2.
  (* left to right *)
  - by apply pmv_full_eq with pmv1.
  (* right to left *)
  - apply pmv_full_eq with pmv2; auto.
Qed.

Lemma pmv_full_add :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 ->
  pmv_full pmv1 \/ pmv_full pmv2 ->
  pmv_full (pmv_add pmv1 pmv2).
Proof.
  intros pmv1 pmv2 H1 H2.
  destruct H2 as [H2 | H2].
  (* [pmv1] is full *)
  - unfold pmv_disj in H1.
    unfold pmv_full, pmv_add in *.
    repeat desf. by apply perm_disj_full_neg_r in H1.
  (* [pmv2] is full *)
  - unfold pmv_disj in H1.
    unfold pmv_full, pmv_add in *.
    repeat desf. by apply perm_disj_full_neg_l in H1.
Qed.

Lemma pmv_disj_full_free :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 ->
  pmv_full pmv1 ->
  pmv2 = PMfree.
Proof.
  intros pmv1 pmv2 H1 H2.
  unfold pmv_disj in H1. unfold pmv_full in H2.
  repeat desf. by apply perm_disj_full_neg_r in H1.
Qed.

Lemma pmv_full_content :
  forall pmv,
  pmv_full pmv ->
  exists p P xs f, pmv = PMelem perm_full p P xs f.
Proof.
  intros pmv H.
  unfold pmv_full in H. desf.
  exists p, P, xs, f. auto.
Qed.

Lemma pmv_full_exp_l :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 ->
  pmv_full pmv1 ->
  pmv_add pmv1 pmv2 = pmv1.
Proof.
  intros pmv1 pmv2 H1 H2.
  apply pmv_disj_full_free in H1; vauto.
  by rewrite pmv_add_iden_l.
Qed.

Lemma pmv_full_exp_r :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 ->
  pmv_full pmv2 ->
  pmv_add pmv1 pmv2 = pmv2.
Proof.
  intros pmv1 pmv2 H1 H2.
  symmetry in H1.
  apply pmv_disj_full_free in H1; vauto.
  by rewrite pmv_add_iden_r.
Qed.


(** *** Shared-memory accesses *)

(** The [pmv_acc] operation gives the list of heap locations that are accessed
    in the given process map value [pmv]. *)

Definition pmv_acc (pmv : ProcMapVal) : list Loc :=
  match pmv with
    | PMelem _ _ _ xs f => map f xs
    | PMfree
    | PMinvalid => nil
  end.

Lemma pmv_acc_eq :
  forall pmv1 pmv2,
  pmv_eq pmv1 pmv2 ->
  pmv_acc pmv1 = pmv_acc pmv2.
Proof.
  intros pmv1 pmv2 H1.
  unfold pmv_eq in H1. unfold pmv_acc.
  repeat desf.
Qed.

Add Parametric Morphism : pmv_acc
  with signature pmv_eq ==> eq
    as pmv_acc_mor.
Proof.
  intros pmv1 pmv2 H1.
  by apply pmv_acc_eq.
Qed.

Lemma pmv_acc_add :
  forall pmv1 pmv2 l,
  pmv_disj pmv1 pmv2 ->
  In l (pmv_acc pmv1) ->
  In l (pmv_acc (pmv_add pmv1 pmv2)).
Proof.
  intros pmv1 pmv2 l H1 H2.
  unfold pmv_disj in H1.
  unfold pmv_acc, pmv_add in *. repeat desf.
Qed.

Lemma pmv_acc_disj_add :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 ->
  pmv_acc pmv1 <> nil ->
  pmv_acc (pmv_add pmv1 pmv2) = pmv_acc pmv1.
Proof.
  intros pmv1 pmv2 H1 H2.
  unfold pmv_disj, pmv_acc, pmv_add in *.
  repeat desf.
Qed.


(** *** Process map entry covering *)

(** The [pmv_covers] predicate determines whether all heap locations accessed
    in a given process map entry [pmv] are _covered_ (i.e. contain a value) in the given heap [h]. *)

Definition pmv_covers (pmv : ProcMapVal)(h : Heap) : Prop :=
  forall l : Loc, In l (pmv_acc pmv) -> exists v : Val, h l = Some v.

Lemma pmv_covers_eq :
  forall pmv1 pmv2 h,
  pmv_eq pmv1 pmv2 ->
  pmv_covers pmv1 h ->
  pmv_covers pmv2 h.
Proof.
  intros pmv1 pmv2 h H1 H2. unfold pmv_covers in *.
  intros l H3. rewrite <- H1 in H3. by apply H2 in H3.
Qed.

Add Parametric Morphism : pmv_covers
  with signature pmv_eq ==> eq ==> iff
    as pmv_covers_mor.
Proof.
  intros pmv1 pmv2 H1 h. split; intro H2.
  - apply pmv_covers_eq with pmv1; auto.
  - apply pmv_covers_eq with pmv2; auto.
Qed.

Lemma pmv_covers_iden :
  forall h,
  pmv_covers PMfree h.
Proof.
  intros h. red. intros l H1. simpl in H1. vauto.
Qed.

Lemma pmv_covers_add :
  forall pmv1 pmv2 h,
  pmv_disj pmv1 pmv2 ->
  pmv_covers (pmv_add pmv1 pmv2) h ->
  pmv_covers pmv1 h.
Proof.
  intros pmv1 pmv2 h H1 H2. unfold pmv_covers in *.
  intros l H3. apply H2. by apply pmv_acc_add.
Qed.

Lemma pmv_covers_heap_upd :
  forall pmv h l v,
  ~ In l (pmv_acc pmv) ->
  pmv_covers pmv h ->
  pmv_covers pmv (update h l v).
Proof.
  intros pmv h l v H1 H2. unfold pmv_covers in *. intros l' H3.
  assert (H4 : l <> l'). { intro H4. apply H1. vauto. }
  apply H2 in H3. destruct H3 as (v' & H3).
  exists v'. unfold update. desf.
Qed.

Lemma pmv_covers_agrees :
  forall pmv h1 h2,
    (forall l, In l (pmv_acc pmv) -> h1 l = h2 l) ->
  pmv_covers pmv h1 ->
  pmv_covers pmv h2.
Proof.
  intros pmv h1 h2 H1 H2. unfold pmv_covers in *.
  intros l H3. generalize H3. intro H4.
  apply H2 in H3. destruct H3 as (v & H3).
  exists v. rewrite <- H1; vauto.
Qed.

Lemma pmv_covers_subheap :
  forall pmv h1 h2,
    (forall l v, h1 l = Some v -> h2 l = Some v) ->
  pmv_covers pmv h1 ->
  pmv_covers pmv h2.
Proof.
  intros pmv h1 h2 H1 H2. unfold pmv_covers in *.
  intros l H3. apply H2 in H3. destruct H3 as (v & H3).
  exists v. by apply H1.
Qed.

Lemma pmv_covers_occ :
  forall pmv h1 h2,
    (forall l : Loc, h1 l <> None -> h2 l <> None) ->
  pmv_covers pmv h1 ->
  pmv_covers pmv h2.
Proof.
  intros pmv h1 h2 H1 H2. unfold pmv_covers in *.
  intros l H3. apply H2 in H3. destruct H3 as (v & H3).
  assert (H4 : h1 l <> None). { intro H4. vauto. }
  apply H1 in H4.
  assert (H5 : exists v' : Val, h2 l = Some v'). { by apply option_not_none. }
  destruct H5 as (v' & H5). by exists v'.
Qed.


(** *** Agreement *)

(** The operation [pmv_agree] defined _agreement_ of the static components
    of two given process map values. *)

Definition pmv_agree (pmv1 pmv2 : ProcMapVal) : Prop :=
  match pmv1, pmv2 with
    | PMfree, PMfree
    | PMinvalid, PMinvalid => True
    | PMelem q1 p1 _ xs1 F1, PMelem q2 p2 _ xs2 F2 =>
        q1 = q2 /\ p1 = p2 /\ xs1 = xs2 /\ map F1 xs1 = map F2 xs2
    | _, _ => False
  end.

(** Process map value agreement is an equivalence relation. *)

Instance pmv_agree_refl :
  Reflexive pmv_agree.
Proof.
  intros pmv. red. desf.
Qed.

Instance pmv_agree_symm :
  Symmetric pmv_agree.
Proof.
  intros pmv1 pmv2 H1.
  unfold pmv_agree in *. repeat desf.
Qed.

Hint Resolve pmv_agree_refl pmv_agree_symm.

Instance pmv_agree_trans :
  Transitive pmv_agree.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2.
  unfold pmv_agree in *.
  repeat desf. intuition vauto.
  by rewrite H7, H4.
Qed.

Instance pmv_agree_equiv :
  Equivalence pmv_agree.
Proof.
  split; intuition.
Qed.

(** Standard operations on [pmv_agree]. *)

Lemma pmv_agree_eq :
  forall pmv1 pmv2,
  pmv_eq pmv1 pmv2 ->
  pmv_agree pmv1 pmv2.
Proof.
  intros pmv1 pmv2 H1.
  unfold pmv_eq, pmv_agree in *.
  repeat desf.
Qed.

Lemma pmv_agree_eq_l :
  forall pmv1 pmv2 pmv3,
  pmv_eq pmv1 pmv2 ->
  pmv_agree pmv1 pmv3 ->
  pmv_agree pmv2 pmv3.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2.
  unfold pmv_eq, pmv_agree in *.
  repeat desf. intuition vauto.
  by rewrite <- H8, H4.
Qed.

Lemma pmv_agree_eq_r :
  forall pmv1 pmv2 pmv3,
  pmv_eq pmv1 pmv2 ->
  pmv_agree pmv3 pmv1 ->
  pmv_agree pmv3 pmv2.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2. symmetry.
  apply pmv_agree_eq_l with pmv1; auto.
Qed.

Add Parametric Morphism : pmv_agree
  with signature pmv_eq ==> pmv_eq ==> iff
    as pmv_agree_eq_mor.
Proof.
  intros pmv1 pmv2 H1 pmv3 pmv4 H2.
  split; intro H3.
  - apply pmv_agree_eq_l with pmv1; auto.
    apply pmv_agree_eq_r with pmv3; auto.
  - apply pmv_agree_eq_l with pmv2; auto.
    apply pmv_agree_eq_r with pmv4; auto.
Qed.

Lemma pmv_disj_agree_l :
  forall pmv1 pmv2 pmv3,
  pmv_agree pmv1 pmv2 ->
  pmv_disj pmv1 pmv3 ->
  pmv_disj pmv2 pmv3.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2.
  unfold pmv_agree, pmv_disj in *.
  repeat desf. intuition vauto.
  by rewrite <- H7, H4.
Qed.

Lemma pmv_disj_agree_r :
  forall pmv1 pmv2 pmv3,
  pmv_agree pmv1 pmv2 ->
  pmv_disj pmv3 pmv1 ->
  pmv_disj pmv3 pmv2.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2. symmetry.
  apply pmv_disj_agree_l with pmv1; auto.
Qed.

Add Parametric Morphism : pmv_disj
  with signature pmv_agree ==> pmv_agree ==> iff
    as pmv_disj_agree_mor.
Proof.
  intros pmv1 pmv2 H1 pmv3 pmv4 H2.
  split; intro H3.
  - apply pmv_disj_agree_l with pmv1; auto.
    apply pmv_disj_agree_r with pmv3; auto.
  - apply pmv_disj_agree_l with pmv2; auto.
    apply pmv_disj_agree_r with pmv4; auto.
Qed.

Lemma pmv_agree_add_l :
  forall pmv1 pmv2 pmv3,
  pmv_agree pmv1 pmv2 ->
  pmv_agree (pmv_add pmv1 pmv3) (pmv_add pmv2 pmv3).
Proof.
  intros pmv1 pmv2 pmv3 H1.
  unfold pmv_agree, pmv_add in *. repeat desf.
  - rewrite H3 in e. congruence.
  - rewrite H3 in n. congruence.
Qed.

Lemma pmv_agree_add_r :
  forall pmv1 pmv2 pmv3,
  pmv_agree pmv1 pmv2 ->
  pmv_agree (pmv_add pmv3 pmv1) (pmv_add pmv3 pmv2).
Proof.
  intros pmv1 pmv2 pmv3 H1.
  rewrite pmv_add_comm with (pmv2 := pmv1).
  rewrite pmv_add_comm with (pmv2 := pmv2).
  by apply pmv_agree_add_l.
Qed.

Lemma pmv_acc_agree :
  forall pmv1 pmv2,
  pmv_agree pmv1 pmv2 ->
  pmv_acc pmv1 = pmv_acc pmv2.
Proof.
  intros pmv1 pmv2 H1.
  unfold pmv_agree in H1. repeat desf.
Qed.

Add Parametric Morphism : pmv_acc
  with signature pmv_agree ==> eq
    as pmv_acc_agree_mor.
Proof.
  intros pmv1 pmv2 H1. by apply pmv_acc_agree.
Qed.

Lemma pmv_covers_agree :
  forall pmv1 pmv2 h,
  pmv_agree pmv1 pmv2 ->
  pmv_covers pmv1 h ->
  pmv_covers pmv2 h.
Proof.
  intros pmv1 pmv2 h H1 H2 l IN1.
  red in H2. specialize H2 with l.
  rewrite pmv_acc_agree with pmv1 pmv2 in H2; auto.
Qed.


(** *** Weak agreement *)

(** The operation [pmv_weak_agree] defined _weak agreement_ of the
    static components of two given process map values. The difference with
    [pmv_agree] is that the permission components are not involved. *)

Definition pmv_weak_agree (pmv1 pmv2 : ProcMapVal) : Prop :=
  match pmv1, pmv2 with
    | PMfree, PMfree
    | PMinvalid, PMinvalid => True
    | PMelem _ p1 _ xs1 F1, PMelem _ p2 _ xs2 F2 =>
        p1 = p2 /\ xs1 = xs2 /\ map F1 xs1 = map F2 xs2
    | _, _ => False
  end.

(** Process map value agreement is an equivalence relation. *)

Instance pmv_weak_agree_refl :
  Reflexive pmv_weak_agree.
Proof.
  intros pmv. red. desf.
Qed.

Instance pmv_weak_agree_symm :
  Symmetric pmv_weak_agree.
Proof.
  intros pmv1 pmv2 H1.
  unfold pmv_weak_agree in *.
  repeat desf.
Qed.

Hint Resolve pmv_weak_agree_refl pmv_weak_agree_symm.

Instance pmv_weak_agree_trans :
  Transitive pmv_weak_agree.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2.
  unfold pmv_weak_agree in *.
  repeat desf. intuition vauto.
  by rewrite H5, H3.
Qed.

Instance pmv_weak_agree_equiv :
  Equivalence pmv_weak_agree.
Proof.
  split; intuition.
Qed.

(** Standard operations on [pmv_weak_agree]. *)

Lemma pmv_weak_agree_eq :
  forall pmv1 pmv2,
  pmv_eq pmv1 pmv2 ->
  pmv_weak_agree pmv1 pmv2.
Proof.
  intros pmv1 pmv2 H1.
  unfold pmv_eq, pmv_weak_agree in *.
  repeat desf.
Qed.

Lemma pmv_weak_agree_eq_l :
  forall pmv1 pmv2 pmv3,
  pmv_eq pmv1 pmv2 ->
  pmv_weak_agree pmv1 pmv3 ->
  pmv_weak_agree pmv2 pmv3.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2.
  unfold pmv_eq, pmv_weak_agree in *.
  repeat desf. intuition vauto.
  by rewrite <- H7, H3.
Qed.

Lemma pmv_weak_agree_eq_r :
  forall pmv1 pmv2 pmv3,
  pmv_eq pmv1 pmv2 ->
  pmv_weak_agree pmv3 pmv1 ->
  pmv_weak_agree pmv3 pmv2.
Proof.
  intros pmv1 pmv2 pmv3 H1 H2. symmetry.
  apply pmv_weak_agree_eq_l with pmv1; auto.
Qed.

Add Parametric Morphism : pmv_weak_agree
  with signature pmv_eq ==> pmv_eq ==> iff
    as pmv_weak_agree_eq_mor.
Proof.
  intros pmv1 pmv2 H1 pmv3 pmv4 H2.
  split; intro H3.
  - apply pmv_weak_agree_eq_l with pmv1; auto.
    apply pmv_weak_agree_eq_r with pmv3; auto.
  - apply pmv_weak_agree_eq_l with pmv2; auto.
    apply pmv_weak_agree_eq_r with pmv4; auto.
Qed.

Lemma pmv_weak_agree_add_l :
  forall pmv1 pmv2 pmv3,
  pmv_weak_agree pmv1 pmv2 ->
  pmv_weak_agree (pmv_add pmv1 pmv3) (pmv_add pmv2 pmv3).
Proof.
  intros pmv1 pmv2 pmv3 H1.
  unfold pmv_weak_agree, pmv_add in *.
  repeat desf.
  - rewrite H2 in e. congruence.
  - rewrite H2 in n. congruence.
Qed.

Lemma pmv_weak_agree_add_r :
  forall pmv1 pmv2 pmv3,
  pmv_weak_agree pmv1 pmv2 ->
  pmv_weak_agree (pmv_add pmv3 pmv1) (pmv_add pmv3 pmv2).
Proof.
  intros pmv1 pmv2 pmv3 H1.
  rewrite pmv_add_comm with (pmv2 := pmv1).
  rewrite pmv_add_comm with (pmv2 := pmv2).
  by apply pmv_weak_agree_add_l.
Qed.

Lemma pmv_acc_weak_agree :
  forall pmv1 pmv2,
  pmv_weak_agree pmv1 pmv2 ->
  pmv_acc pmv1 = pmv_acc pmv2.
Proof.
  intros pmv1 pmv2 H1.
  unfold pmv_weak_agree in H1. repeat desf.
Qed.

Add Parametric Morphism : pmv_acc
  with signature pmv_weak_agree ==> eq
    as pmv_acc_weak_agree_mor.
Proof.
  intros pmv1 pmv2 H1.
  by apply pmv_acc_weak_agree.
Qed.

Lemma pmv_agree_weaken :
  forall pmv1 pmv2,
  pmv_agree pmv1 pmv2 ->
  pmv_weak_agree pmv1 pmv2.
Proof.
  intros pmv1 pmv2 H1.
  unfold pmv_agree, pmv_weak_agree in *.
  repeat desf.
Qed.


(** *** Occupation *)

(** The operation [pmv_occ] determines whether a given process map entry
    is _occupied_ (i.e. contains some element). *)

Definition pmv_occ (pmv : ProcMapVal) : Prop :=
  match pmv with
    | PMelem _ _ _ _ _ => True
    | _ => False
  end.

Lemma pmv_occ_eq :
  forall pmv1 pmv2,
  pmv_eq pmv1 pmv2 ->
  pmv_occ pmv1 ->
  pmv_occ pmv2.
Proof.
  intros pmv1 pmv2 H1 H2.
  unfold pmv_eq, pmv_occ in *. desf.
Qed.

Add Parametric Morphism : pmv_occ
  with signature pmv_eq ==> iff
    as pmv_occ_eq_mor.
Proof.
  intros pmv1 pmv2 H1. split; intro H2.
  - apply pmv_occ_eq with pmv1; auto.
  - apply pmv_occ_eq with pmv2; auto.
Qed.

Lemma pmv_occ_agree :
  forall pmv1 pmv2,
  pmv_agree pmv1 pmv2 ->
  pmv_occ pmv1 ->
  pmv_occ pmv2.
Proof.
  intros pmv1 pmv2 H1 H2.
  unfold pmv_agree, pmv_occ in *. desf.
Qed.

Add Parametric Morphism : pmv_occ
  with signature pmv_agree ==> iff
    as pmv_occ_agree_mor.
Proof.
  intros pmv1 pmv2 H1. split; intro H2.
  - apply pmv_occ_agree with pmv1; auto.
  - apply pmv_occ_agree with pmv2; auto.
Qed.

Lemma pmv_occ_add_l :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 ->
  pmv_occ pmv1 ->
  pmv_occ (pmv_add pmv1 pmv2).
Proof.
  intros pmv1 pmv2 H1 H2.
  unfold pmv_disj, pmv_occ, pmv_add in *.
  repeat desf.
Qed.

Lemma pmv_occ_add_r :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 ->
  pmv_occ pmv2 ->
  pmv_occ (pmv_add pmv1 pmv2).
Proof.
  intros pmv1 pmv2 H1 H2.
  rewrite pmv_add_comm.
  apply pmv_occ_add_l; auto.
Qed.

Lemma pmv_occ_destruct :
  forall pmv,
  pmv_occ pmv ->
  exists q p P xs f, pmv = PMelem q p P xs f.
Proof.
  intros pmv H. unfold pmv_occ in H.
  desf. by exists q, p, P, xs, f.
Qed.

Lemma pmv_weak_agree_add_occ :
  forall pmv1 pmv2,
  pmv_disj pmv1 pmv2 ->
  pmv_occ pmv1 ->
  pmv_weak_agree pmv1 (pmv_add pmv1 pmv2).
Proof.
  intros pmv1 pmv2 H1 H2.
  unfold pmv_disj, pmv_add, pmv_occ, pmv_weak_agree in *.
  repeat desf.
Qed.


(** ** Process maps *)

Definition ProcMap := ProcID -> ProcMapVal.
Definition procmap_iden : ProcMap := fun _ => PMfree.


(** *** Equality (up to bisimulation) *)

(** Two process maps are _equal_ (up to bisimulation) if all their mappings are equal pairwise. *)

Definition procmap_eq (pm1 pm2 : ProcMap) : Prop :=
  forall pid : ProcID, pmv_eq (pm1 pid) (pm2 pid).

Notation "A ≈ B" := (procmap_eq A B) (only printing, at level 80).

Instance procmap_eq_refl :
  Reflexive procmap_eq.
Proof. red.
  red. by ins.
Qed.

Hint Resolve procmap_eq_refl.

Instance procmap_eq_symm :
  Symmetric procmap_eq.
Proof.
  intros ????. by symmetry.
Qed.

Hint Resolve procmap_eq_symm.

Instance procmap_eq_trans :
  Transitive procmap_eq.
Proof.
  intros ? pm ??? pid.
  by transitivity (pm pid).
Qed.

Instance procmap_eq_equiv :
  Equivalence procmap_eq.
Proof.
  split; intuition.
Qed.

Lemma procmap_update_eq :
  forall pm1 pm2 pid pmv,
  procmap_eq pm1 pm2 ->
  procmap_eq (update pm1 pid pmv) (update pm2 pid pmv).
Proof.
  intros ?? pid ? H pid'.
  unfold procmap_eq, update in *.
  specialize H with pid'.
  case (Z.eq_dec pid pid'); ins.
Qed.

Add Parametric Morphism : update
  with signature procmap_eq ==> eq ==> pmv_eq ==> procmap_eq
    as procmap_update_mor.
Proof.
  intros pm1 pm2 H1 pid pmv1 pmv2 H2 pid'.
  unfold update. desf.
Qed.

Lemma procmap_eq_free :
  forall pm1 pm2 pid,
  procmap_eq pm1 pm2 -> pm1 pid = PMfree -> pm2 pid = PMfree.
Proof.
  intros pm1 pm2 pid H1 H2.
  by apply pmv_eq_free with (pm1 pid).
Qed.


(** *** Validity *)

(** A process map is _valid_ if all its mappings are valid. *)

Definition procmap_valid (pm : ProcMap) : Prop :=
  forall pid : ProcID, pmv_valid (pm pid).

Notation "√ pm" := (procmap_valid pm) (only printing, at level 80).

Lemma procmap_eq_valid :
  forall pm1 pm2,
  procmap_eq pm1 pm2 ->
  procmap_valid pm1 -> procmap_valid pm2.
Proof.
  intros pm1 pm2 H1 H2 pid.
  unfold procmap_eq, procmap_valid in *.
  specialize H1 with pid.
  by rewrite <- H1.
Qed.

Add Parametric Morphism : procmap_valid
  with signature procmap_eq ==> iff
    as procmap_valid_mor.
Proof.
  intros pm1 pm1' H1.
  split; intro H2.
  by apply procmap_eq_valid with pm1.
  apply procmap_eq_valid with pm1'; auto.
Qed.

Lemma procmap_valid_iden :
  procmap_valid procmap_iden.
Proof.
  red. ins.
Qed.

Hint Resolve procmap_valid_iden.

Lemma procmap_valid_upd :
  forall pmv pm pid,
  pmv_valid pmv ->
  procmap_valid pm ->
  procmap_valid (update pm pid pmv).
Proof.
  intros ??????. unfold update. desf.
Qed.


(** *** Disjointness *)

(** Two process maps are disjoint if all their mappings are disjoint pairwise. *)

Definition procmap_disj (pm1 pm2 : ProcMap) : Prop :=
  forall pid : ProcID, pmv_disj (pm1 pid) (pm2 pid).

Notation "A ⟂ B" := (procmap_disj A B) (only printing, at level 80).

Instance procmap_disj_symm :
  Symmetric procmap_disj.
Proof.
  intros ????. by symmetry.
Qed.

Hint Resolve procmap_disj_symm.

Lemma procmap_disj_eq_l :
  forall pm1 pm2 pm,
  procmap_eq pm1 pm2 -> procmap_disj pm1 pm -> procmap_disj pm2 pm.
Proof.
  unfold procmap_eq, procmap_disj.
  intros ??? H ??. by rewrite <- H.
Qed.

Lemma procmap_disj_eq_r :
  forall pm1 pm2 pm,
  procmap_eq pm1 pm2 -> procmap_disj pm pm1 -> procmap_disj pm pm2.
Proof.
  unfold procmap_eq, procmap_disj.
  intros ??? H ??. by rewrite <- H.
Qed.

Add Parametric Morphism : procmap_disj
  with signature procmap_eq ==> procmap_eq ==> iff
    as procmap_disj_mor.
Proof.
  intros pm1 pm1' H1 pm2 pm2' H2.
  split; intro H.
  apply procmap_disj_eq_l with pm1; auto.
  apply procmap_disj_eq_r with pm2; auto.
  apply procmap_disj_eq_l with pm1'; auto.
  apply procmap_disj_eq_r with pm2'; auto.
Qed.

Lemma procmap_disj_valid_l :
  forall pm1 pm2, procmap_disj pm1 pm2 -> procmap_valid pm1.
Proof.
  intros ? pm ? pid.
  by apply pmv_disj_valid_l with (pm pid).
Qed.

Lemma procmap_disj_valid_r :
  forall pm1 pm2, procmap_disj pm1 pm2 -> procmap_valid pm2.
Proof.
  intros pm ?? pid.
  by apply pmv_disj_valid_r with (pm pid).
Qed.

Lemma procmap_disj_valid :
  forall pm1 pm2,
  procmap_disj pm1 pm2 -> procmap_valid pm1 /\ procmap_valid pm2.
Proof.
  intros pm1 pm2 H. intuition.
  by apply procmap_disj_valid_l with pm2.
  by apply procmap_disj_valid_r with pm1.
Qed.

Lemma procmap_disj_iden_l :
  forall pm, procmap_valid pm -> procmap_disj pm procmap_iden.
Proof.
  unfold procmap_valid, procmap_iden.
  intros ???. by apply pmv_disj_iden_l.
Qed.

Hint Resolve procmap_disj_iden_l.

Lemma procmap_disj_iden_r :
  forall pm, procmap_valid pm -> procmap_disj procmap_iden pm.
Proof.
  unfold procmap_valid, procmap_iden.
  intros ???. by apply pmv_disj_iden_r.
Qed.

Hint Resolve procmap_disj_iden_r.

Lemma procmap_disj_upd :
  forall pmv1 pmv2 pm1 pm2 pid,
  pmv_disj pmv1 pmv2 ->
  procmap_disj pm1 pm2 ->
  procmap_disj (update pm1 pid pmv1) (update pm2 pid pmv2).
Proof.
  unfold procmap_disj, update.
  intros ????????. desf.
Qed.


(** *** Addition *)

(** The addition of two process maps [pm1] and [pm2] is defined as the
    process map that adds the mappings of [pm1] and [pm2]. *)

Definition procmap_add (pm1 pm2 : ProcMap) : ProcMap :=
  fun pid : ProcID => pmv_add (pm1 pid) (pm2 pid).

Notation "A ⊕ B" := (procmap_add A B) (only printing, at level 80, right associativity).

Lemma procmap_add_eq_l :
  forall pm1 pm2 pm,
  procmap_eq pm1 pm2 ->
  procmap_eq (procmap_add pm1 pm) (procmap_add pm2 pm).
Proof.
  unfold procmap_eq, procmap_add.
  ins. by rewrite <- H.
Qed.

Lemma procmap_add_eq_r :
  forall pm1 pm2 pm,
  procmap_eq pm1 pm2 ->
  procmap_eq (procmap_add pm pm1) (procmap_add pm pm2).
Proof.
  unfold procmap_eq, procmap_add.
  ins. by rewrite <- H.
Qed.

Add Parametric Morphism : procmap_add
  with signature procmap_eq ==> procmap_eq ==> procmap_eq
    as procmap_add_mor.
Proof.
  intros pm1 pm1' H1 pm2 pm2' H2.
  transitivity (procmap_add pm1' pm2).
  by apply procmap_add_eq_l.
  by apply procmap_add_eq_r.
Qed.

Lemma procmap_add_iden_l :
  forall pm, procmap_add pm procmap_iden = pm.
Proof.
  intro pm. extensionality pid.
  unfold procmap_add, procmap_iden.
  apply pmv_add_iden_l.
Qed.

Hint Rewrite procmap_add_iden_l.

Lemma procmap_add_iden_r :
  forall pm, procmap_add procmap_iden pm = pm.
Proof.
  intro pm. extensionality pid.
  unfold procmap_add, procmap_iden.
  apply pmv_add_iden_r.
Qed.

Hint Rewrite procmap_add_iden_r.

Lemma procmap_add_assoc :
  forall pm1 pm2 pm3,
  procmap_eq (procmap_add (procmap_add pm1 pm2) pm3) (procmap_add pm1 (procmap_add pm2 pm3)).
Proof.
  intros ????. apply pmv_add_assoc.
Qed.

Hint Resolve procmap_add_assoc.

Lemma procmap_add_comm :
  forall pm1 pm2,
  procmap_eq (procmap_add pm1 pm2) (procmap_add pm2 pm1).
Proof.
  intros ???. by apply pmv_add_comm.
Qed.

Lemma procmap_add_valid :
  forall pm1 pm2,
  procmap_disj pm1 pm2 ->
  procmap_valid (procmap_add pm1 pm2).
Proof.
  unfold procmap_add. intros ????.
  by apply pmv_add_valid.
Qed.

Hint Resolve procmap_add_valid.

Lemma procmap_disj_add_l :
  forall pm1 pm2 pm3,
  procmap_disj pm1 pm2 ->
  procmap_disj (procmap_add pm1 pm2) pm3 ->
  procmap_disj pm2 pm3.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  apply pmv_disj_add_l with (pm1 pid); auto.
  by apply H2.
Qed.

Lemma procmap_disj_add_r :
  forall pm1 pm2 pm3,
  procmap_disj pm2 pm3 ->
  procmap_disj pm1 (procmap_add pm2 pm3) ->
  procmap_disj pm1 pm2.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  apply pmv_disj_add_r with (pm3 pid); auto.
  by apply H2.
Qed.

Lemma procmap_disj_assoc_l :
  forall pm1 pm2 pm3,
  procmap_disj pm1 pm2 ->
  procmap_disj (procmap_add pm1 pm2) pm3 ->
  procmap_disj pm1 (procmap_add pm2 pm3).
Proof.
  intros ???? H ?.
  apply pmv_disj_assoc_l. auto. apply H.
Qed.

Lemma procmap_disj_assoc_r :
  forall pm1 pm2 pm3,
  procmap_disj pm2 pm3 ->
  procmap_disj pm1 (procmap_add pm2 pm3) ->
  procmap_disj (procmap_add pm1 pm2) pm3.
Proof.
  intros ???? H ?.
  apply pmv_disj_assoc_r. auto. apply H.
Qed.

Lemma procmap_disj_swap_r :
  forall pm1 pm2 pm3,
  procmap_disj pm1 pm2 ->
  procmap_disj (procmap_add pm1 pm2) pm3 ->
  procmap_disj (procmap_add pm1 pm3) pm2.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  apply pmv_disj_swap_r; auto.
  by apply H2.
Qed.

Lemma procmap_disj_swap_l :
  forall pm1 pm2 pm3,
  procmap_disj pm1 pm2 ->
  procmap_disj (procmap_add pm1 pm2) pm3 ->
  procmap_disj (procmap_add pm2 pm3) pm1.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  apply pmv_disj_swap_l; auto.
  by apply H2.
Qed.

Lemma procmap_add_upd :
  forall pm1 pm2 pmv1 pmv2 pid,
  update (procmap_add pm1 pm2) pid (pmv_add pmv1 pmv2) =
  procmap_add (update pm1 pid pmv1) (update pm2 pid pmv2).
Proof.
  ins. extensionality pid'.
  unfold procmap_add, update. desf.
Qed.

Lemma procmap_add_pmv :
  forall pm1 pm2 pid,
  pmv_add (pm1 pid) (pm2 pid) = procmap_add pm1 pm2 pid.
Proof.
  ins.
Qed.

Lemma procmap_disj_middle :
  forall pm1 pm2 pm3 pm4,
  procmap_disj pm1 pm2 ->
  procmap_disj pm3 pm4 ->
  procmap_disj (procmap_add pm1 pm2) (procmap_add pm3 pm4) ->
  procmap_disj pm2 pm3.
Proof.
  intros pm1 pm2 pm3 pm4 H1 H2 H3.
  apply procmap_disj_add_l with pm1; auto.
  by apply procmap_disj_add_r with pm4.
Qed.

Lemma procmap_disj_compat :
  forall pm1 pm2 pm3 pm4,
  procmap_disj pm1 pm3 ->
  procmap_disj pm2 pm4 ->
  procmap_disj (procmap_add pm1 pm3) (procmap_add pm2 pm4) ->
  procmap_disj (procmap_add pm1 pm2) (procmap_add pm3 pm4).
Proof.
  intros pm1 pm2 pm3 pm4 H1 H2 H3.
  apply procmap_disj_assoc_r.
  rewrite procmap_add_comm.
  apply procmap_disj_assoc_l; auto.
  symmetry. by apply procmap_disj_add_l in H3.
  rewrite procmap_add_comm.
  rewrite procmap_add_assoc.
  apply procmap_disj_assoc_l; auto.
  by rewrite procmap_add_comm with (pm1:=pm4)(pm2:=pm2).
Qed.

Lemma procmap_add_swap_l :
  forall pm1 pm2 pm3,
  procmap_eq (procmap_add pm1 (procmap_add pm2 pm3))
    (procmap_add pm2 (procmap_add pm1 pm3)).
Proof.
  intros ????. by apply pmv_add_swap_l.
Qed.

Lemma procmap_add_swap_r :
  forall pm1 pm2 pm3,
  procmap_eq (procmap_add (procmap_add pm1 pm2) pm3)
    (procmap_add (procmap_add pm1 pm3) pm2).
Proof.
  intros ????. by apply pmv_add_swap_r.
Qed.

Lemma procmap_add_compat :
  forall pm1 pm2 pm3 pm4,
  procmap_eq (procmap_add (procmap_add pm1 pm3) (procmap_add pm2 pm4))
    (procmap_add (procmap_add pm1 pm2) (procmap_add pm3 pm4)).
Proof.
  intros pm1 pm2 pm3 pm4 pid.
  repeat rewrite <- procmap_add_pmv.
  apply pmv_add_compat.
Qed.


(** *** Finiteness *)

(** A process map is _finite_ if all mappings that are not free can be mapped to some
    finite structure, in this case a list. *)

Definition procmap_finite (pm : ProcMap) : Prop :=
  exists xs : list ProcID,
    forall pid : ProcID, pm pid <> PMfree -> In pid xs.

Lemma procmap_finite_eq :
  forall pm1 pm2,
  procmap_eq pm1 pm2 ->
  procmap_finite pm1 ->
  procmap_finite pm2.
Proof.
  intros pm1 pm2 EQ (xs & F).
  unfold procmap_finite.
  exists xs. intros pid H1.
  apply F. intro H2.
  apply procmap_eq_free with (pm2 := pm2) in H2; vauto.
Qed.

Add Parametric Morphism : procmap_finite
  with signature procmap_eq ==> iff
    as procmap_finite_eq_mor.
Proof.
  intros pm1 pm2 EQ. split; intro H.
  apply procmap_finite_eq with pm1; auto.
  apply procmap_finite_eq with pm2; auto.
Qed.

Lemma procmap_finite_iden :
  procmap_finite procmap_iden.
Proof.
  red. exists nil. intros pid H. vauto.
Qed.

(** The main property of interest of finite process maps, is that one can
    always find a mapping that is free. *)

Lemma procmap_finite_free :
  forall pm,
  procmap_finite pm ->
  exists pid : ProcID, pm pid = PMfree.
Proof.
  intros pm (xs & FIN).
  assert (H : exists pid : ProcID, ~ In pid xs). {
  apply list_Z_max_notin. }
  destruct H as (pid & H).
  specialize FIN with pid.
  exists pid. tauto.
Qed.

Lemma procmap_finite_upd :
  forall pm pid pmv,
  procmap_finite pm ->
  procmap_finite (update pm pid pmv).
Proof.
  intros pm pid pmv (xs & FIN).
  assert (H1 : pmv = PMfree \/ ~ pmv = PMfree). { apply classic. }
  destruct H1 as [H1 | H1].
  (* [pmv] is free *)
  - exists xs. intros pid' H2. apply FIN.
    unfold update in H2. desf.
  (* [pmv] is not free *)
  - exists (pid :: xs).
    intros pid' H2.
    specialize FIN with pid'. simpls.
    unfold update in H2.
    destruct (Z.eq_dec pid pid') as [|H3]; vauto.
    right. by apply FIN.
Qed.

Lemma procmap_finite_add :
  forall pm1 pm2,
  procmap_finite (procmap_add pm1 pm2) <->
  procmap_finite pm1 /\ procmap_finite pm2.
Proof.
  intros pm1 pm2. split.
  (* left to right *)
  - intros (xs & FIN).
    unfold procmap_finite. split.
    (* [pm1] is finite *)
    + exists xs. intros pid H1.
      apply FIN. intro H2.
      apply pmv_add_not_free in H2; vauto.
    (* [pm2] is finite *)
    + exists xs. intros pid H1.
      apply FIN. intro H2.
      apply pmv_add_not_free in H2; vauto.
  (* right to left *)
  - intro FIN.
    destruct FIN as ((xs1 & FIN1) & (xs2 & FIN2)).
    unfold procmap_finite.
    exists (xs1 ++ xs2). intros pid H1.
    apply in_or_app.
    unfold procmap_add in H1.
    apply pmv_add_not_free in H1.
    destruct H1 as [H1 | H1].
    + left. by apply FIN1.
    + right. by apply FIN2.
Qed.


(** *** Shared-memory accesses *)

(** The [procmap_acc] operation determines whether a given heap location [l]
    is accessed in a given process map [pm]. *)

Definition procmap_acc (pm : ProcMap)(l : Loc) : Prop :=
  exists pid : ProcID, In l (pmv_acc (pm pid)).

Lemma procmap_acc_eq :
  forall pm1 pm2 l,
  procmap_eq pm1 pm2 ->
  procmap_acc pm1 l ->
  procmap_acc pm2 l.
Proof.
  intros pm1 pm2 l H1 H2. unfold procmap_acc in *.
  destruct H2 as (pid & H2). exists pid.
  unfold procmap_eq in H1. specialize H1 with pid.
  by rewrite <- H1.
Qed.

Add Parametric Morphism : procmap_acc
  with signature procmap_eq ==> eq ==> iff
    as procmap_acc_mor.
Proof.
  intros pm1 pm2 H1 l. split; intro H2.
  - by apply procmap_acc_eq with pm1.
  - apply procmap_acc_eq with pm2; auto.
Qed.

Lemma procmap_acc_add :
  forall pm1 pm2 l,
  procmap_disj pm1 pm2 ->
  procmap_acc pm1 l ->
  procmap_acc (procmap_add pm1 pm2) l.
Proof.
  intros pm1 pm2 l H1 H2. unfold procmap_acc in *.
  destruct H2 as (pid & H2). exists pid.
  rewrite <- procmap_add_pmv. apply pmv_acc_add; auto.
Qed.


(** *** Process map covering *)

(** The [procmap_covers] predicate determines whether all heap locations accessed
    in a given process map [pm] are _covered_ (i.e. contain a value) in the given heap [h]. *)

Definition procmap_covers (pm : ProcMap)(h : Heap) : Prop :=
  forall pid : ProcID, pmv_covers (pm pid) h.

Lemma procmap_covers_eq :
  forall pm1 pm2 h,
  procmap_eq pm1 pm2 ->
  procmap_covers pm1 h ->
  procmap_covers pm2 h.
Proof.
  intros pm1 pm2 h H1 H2. unfold procmap_covers in *.
  intro pid. by apply pmv_covers_eq with (pm1 pid).
Qed.

Add Parametric Morphism : procmap_covers
  with signature procmap_eq ==> eq ==> iff
    as procmap_covers_mor.
Proof.
  intros pm1 pm2 H1 h. split; intro H2.
  - apply procmap_covers_eq with pm1; auto.
  - apply procmap_covers_eq with pm2; auto.
Qed.

Lemma procmap_covers_iden :
  forall h,
  procmap_covers procmap_iden h.
Proof.
  intros h. red. intros pid. unfold procmap_iden.
  by apply pmv_covers_iden.
Qed.

Lemma procmap_covers_upd :
  forall pm h pid pmv,
    (forall l, In l (pmv_acc pmv) -> exists v, h l = Some v) ->
  procmap_covers pm h ->
  procmap_covers (update pm pid pmv) h.
Proof.
  intros pm h pid pmv H1 H2. unfold procmap_covers in *.
  intro pid'. unfold update. desf.
Qed.

Lemma procmap_covers_heap_upd :
  forall pm h l v,
  ~ procmap_acc pm l ->
  procmap_covers pm h ->
  procmap_covers pm (update h l v).
Proof.
  intros pm h l v H1 H2.
  unfold procmap_covers in *. intro pid.
  apply pmv_covers_heap_upd; vauto. intro H3.
  apply H1. red. exists pid. done.
Qed.

Lemma procmap_covers_add :
  forall pm1 pm2 h,
  procmap_disj pm1 pm2 ->
  procmap_covers (procmap_add pm1 pm2) h ->
  procmap_covers pm1 h.
Proof.
  intros pm1 pm2 h H1 H2. unfold procmap_covers in *.
  intro pid. apply pmv_covers_add with (pm2 pid); vauto.
  specialize H2 with pid. by rewrite <- procmap_add_pmv in H2.
Qed.

Lemma procmap_covers_agrees :
  forall pm h1 h2,
    (forall l, procmap_acc pm l -> h1 l = h2 l) ->
  procmap_covers pm h1 ->
  procmap_covers pm h2.
Proof.
  intros pm h1 h2 H1 H2. unfold procmap_covers in *.
  intro pid. apply pmv_covers_agrees with h1; vauto.
  intros l H3. apply H1. red. exists pid. done.
Qed.

Lemma procmap_covers_subheap :
  forall pm h1 h2,
    (forall l v, h1 l = Some v -> h2 l = Some v) ->
  procmap_covers pm h1 ->
  procmap_covers pm h2.
Proof.
  intros pm h1 h2 H1 H2. unfold procmap_covers in *.
  intro pid. apply pmv_covers_subheap with h1; vauto.
Qed.

Lemma procmap_covers_occ :
  forall pm h1 h2,
    (forall l, h1 l <> None -> h2 l <> None) ->
  procmap_covers pm h1 ->
  procmap_covers pm h2.
Proof.
  intros pm h1 h2 H1 H2. unfold procmap_covers in *.
  intro pid. apply pmv_covers_occ with h1; vauto.
Qed.


(** *** Agreement *)

(** The operator [procmap_agree] determines whether two given
    process maps _agree_ pairwise on the static components of all their mappings. *)

Definition procmap_agree (pm1 pm2 : ProcMap) : Prop :=
  forall pid : ProcID, pmv_agree (pm1 pid) (pm2 pid).

(** The [procmap_agree] relation is an equivalence relation. *)

Instance procmap_agree_refl :
  Reflexive procmap_agree.
Proof.
  red. intros pm pid. auto.
Qed.

Instance procmap_agree_symm :
  Symmetric procmap_agree.
Proof.
  red. intros pm1 pm2 H1 pid.
  symmetry. apply H1.
Qed.

Hint Resolve procmap_agree_refl procmap_agree_symm.

Instance procmap_agree_trans :
  Transitive procmap_agree.
Proof.
  red. intros pm1 pm2 pm3 H1 H2 pid.
  transitivity (pm2 pid).
  - apply H1.
  - apply H2.
Qed.

Instance procmap_agree_equiv :
  Equivalence procmap_agree.
Proof.
  split; intuition.
Qed.

(** Standard operations on [procmap_agree]. *)

Lemma procmap_agree_eq :
  forall pm1 pm2,
  procmap_eq pm1 pm2 ->
  procmap_agree pm1 pm2.
Proof.
  intros pm1 pm2 H pid.
  unfold procmap_eq in H. specialize H with pid.
  by rewrite H.
Qed.

Lemma procmap_agree_eq_l :
  forall pm1 pm2 pm3,
  procmap_eq pm1 pm2 ->
  procmap_agree pm1 pm3 ->
  procmap_agree pm2 pm3.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  unfold procmap_eq in H1. specialize H1 with pid.
  rewrite <- H1. by apply H2.
Qed.

Lemma procmap_agree_eq_r :
  forall pm1 pm2 pm3,
  procmap_eq pm1 pm2 ->
  procmap_agree pm3 pm1 ->
  procmap_agree pm3 pm2.
Proof.
  intros pm1 pm2 pm3 H1 H2. symmetry.
  apply procmap_agree_eq_l with pm1; auto.
Qed.

Add Parametric Morphism : procmap_agree
  with signature procmap_eq ==> procmap_eq ==> iff
    as procmap_agree_eq_mor.
Proof.
  intros pm1 pm2 H1 pm3 pm4 H2. split; intro H3.
  - apply procmap_agree_eq_l with pm1; auto.
    apply procmap_agree_eq_r with pm3; auto.
  - apply procmap_agree_eq_l with pm2; auto.
    apply procmap_agree_eq_r with pm4; auto.
Qed.

Lemma procmap_disj_agree_l :
  forall pm1 pm2 pm3,
  procmap_agree pm1 pm2 ->
  procmap_disj pm1 pm3 ->
  procmap_disj pm2 pm3.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  apply pmv_disj_agree_l with (pm1 pid); auto.
Qed.

Lemma procmap_disj_agree_r :
  forall pm1 pm2 pm3,
  procmap_agree pm1 pm2 ->
  procmap_disj pm3 pm1 ->
  procmap_disj pm3 pm2.
Proof.
  intros pm1 pm2 pm3 H1 H2. symmetry.
  apply procmap_disj_agree_l with pm1; auto.
Qed.

Add Parametric Morphism : procmap_disj
  with signature procmap_agree ==> procmap_agree ==> iff
    as procmap_disj_agree_mor.
Proof.
  intros pm1 pm2 H1 pm3 pm4 H2. split; intro H3.
  - apply procmap_disj_agree_l with pm1; auto.
    apply procmap_disj_agree_r with pm3; auto.
  - apply procmap_disj_agree_l with pm2; auto.
    apply procmap_disj_agree_r with pm4; auto.
Qed.

Lemma procmap_agree_add_l :
  forall pm1 pm2 pm3,
  procmap_agree pm1 pm2 ->
  procmap_agree (procmap_add pm1 pm3) (procmap_add pm2 pm3).
Proof.
  intros pm1 pm2 pm3 H1 pid.
  repeat rewrite <- procmap_add_pmv.
  by apply pmv_agree_add_l.
Qed.

Lemma procmap_agree_add_r :
  forall pm1 pm2 pm3,
  procmap_agree pm1 pm2 ->
  procmap_agree (procmap_add pm3 pm1) (procmap_add pm3 pm2).
Proof.
  intros pm1 pm2 pm3 H1 pid.
  repeat rewrite <- procmap_add_pmv.
  by apply pmv_agree_add_r.
Qed.

Lemma procmap_finite_agree :
  forall pm1 pm2,
  procmap_agree pm1 pm2 ->
  procmap_finite pm1 ->
  procmap_finite pm2.
Proof.
  intros pm1 pm2 H1 H2.
  red in H2. destruct H2 as (xs & H2).
  exists xs. intros pid H3.
  apply H2. intro H4. apply H3.
  unfold procmap_agree in H1. specialize H1 with pid.
  rewrite H4 in H1. red in H1. desf.
Qed.

Add Parametric Morphism : procmap_finite
  with signature procmap_agree ==> iff
    as procmap_finite_agree_mor.
Proof.
  intros pm1 pm2 H1. split; intro H2.
  - apply procmap_finite_agree with pm1; auto.
  - apply procmap_finite_agree with pm2; auto.
Qed.

Lemma procmap_covers_agree :
  forall pm1 pm2 h,
  procmap_agree pm1 pm2 ->
  procmap_covers pm1 h ->
  procmap_covers pm2 h.
Proof.
  intros pm1 pm2 h H1 H2 pid.
  apply pmv_covers_agree with (pm1 pid); auto.
Qed.


(** *** Weak agreement *)

(** The operator [procmap_weak_agree] determines whether two given
    process maps _weakly agree_ pairwise on the components of all their mappings. *)

Definition procmap_weak_agree (pm1 pm2 : ProcMap) : Prop :=
  forall pid : ProcID, pmv_weak_agree (pm1 pid) (pm2 pid).

(** The [procmap_weak_agree] relation is an equivalence relation. *)

Instance procmap_weak_agree_refl :
  Reflexive procmap_weak_agree.
Proof.
  red. intros pm pid. auto.
Qed.

Instance procmap_weak_agree_symm :
  Symmetric procmap_weak_agree.
Proof.
  red. intros pm1 pm2 H1 pid.
  symmetry. apply H1.
Qed.

Hint Resolve procmap_weak_agree_refl procmap_weak_agree_symm.

Instance procmap_weak_agree_trans :
  Transitive procmap_weak_agree.
Proof.
  red. intros pm1 pm2 pm3 H1 H2 pid.
  transitivity (pm2 pid).
  - apply H1.
  - apply H2.
Qed.

Instance procmap_weak_agree_equiv :
  Equivalence procmap_weak_agree.
Proof.
  split; intuition.
Qed.

(** Standard operations on [procmap_weak_agree]. *)

Lemma procmap_weak_agree_eq :
  forall pm1 pm2,
  procmap_eq pm1 pm2 ->
  procmap_weak_agree pm1 pm2.
Proof.
  intros pm1 pm2 H pid.
  unfold procmap_eq in H. specialize H with pid.
  by rewrite H.
Qed.

Lemma procmap_weak_agree_eq_l :
  forall pm1 pm2 pm3,
  procmap_eq pm1 pm2 ->
  procmap_weak_agree pm1 pm3 ->
  procmap_weak_agree pm2 pm3.
Proof.
  intros pm1 pm2 pm3 H1 H2 pid.
  unfold procmap_eq in H1. specialize H1 with pid.
  rewrite <- H1. by apply H2.
Qed.

Lemma procmap_weak_agree_eq_r :
  forall pm1 pm2 pm3,
  procmap_eq pm1 pm2 ->
  procmap_weak_agree pm3 pm1 ->
  procmap_weak_agree pm3 pm2.
Proof.
  intros pm1 pm2 pm3 H1 H2. symmetry.
  apply procmap_weak_agree_eq_l with pm1; auto.
Qed.

Add Parametric Morphism : procmap_weak_agree
  with signature procmap_eq ==> procmap_eq ==> iff
    as procmap_weak_agree_eq_mor.
Proof.
  intros pm1 pm2 H1 pm3 pm4 H2. split; intro H3.
  - apply procmap_weak_agree_eq_l with pm1; auto.
    apply procmap_weak_agree_eq_r with pm3; auto.
  - apply procmap_weak_agree_eq_l with pm2; auto.
    apply procmap_weak_agree_eq_r with pm4; auto.
Qed.

Lemma procmap_weak_agree_add_l :
  forall pm1 pm2 pm3,
  procmap_weak_agree pm1 pm2 ->
  procmap_weak_agree (procmap_add pm1 pm3) (procmap_add pm2 pm3).
Proof.
  intros pm1 pm2 pm3 H1 pid.
  repeat rewrite <- procmap_add_pmv.
  by apply pmv_weak_agree_add_l.
Qed.

Lemma procmap_weak_agree_add_r :
  forall pm1 pm2 pm3,
  procmap_weak_agree pm1 pm2 ->
  procmap_weak_agree (procmap_add pm3 pm1) (procmap_add pm3 pm2).
Proof.
  intros pm1 pm2 pm3 H1 pid.
  repeat rewrite <- procmap_add_pmv.
  by apply pmv_weak_agree_add_r.
Qed.

Lemma procmap_finite_weak_agree :
  forall pm1 pm2,
  procmap_weak_agree pm1 pm2 ->
  procmap_finite pm1 ->
  procmap_finite pm2.
Proof.
  intros pm1 pm2 H1 H2.
  red in H2. destruct H2 as (xs & H2).
  exists xs. intros pid H3.
  apply H2. intro H4. apply H3.
  unfold procmap_weak_agree in H1. specialize H1 with pid.
  rewrite H4 in H1. red in H1. desf.
Qed.

Add Parametric Morphism : procmap_finite
  with signature procmap_weak_agree ==> iff
    as procmap_finite_weak_agree_mor.
Proof.
  intros pm1 pm2 H1. split; intro H2.
  - apply procmap_finite_weak_agree with pm1; auto.
  - apply procmap_finite_weak_agree with pm2; auto.
Qed.
