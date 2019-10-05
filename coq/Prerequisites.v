Require Import Equalities.
Require Import HahnBase.
Require Import List.
Require Import ListSet.
Require Import Permutation.
Require Import PermutationTactic.
Require Import Setoid.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.

Set Implicit Arguments.

Lemma ex_iff :
  forall A p q (EQ: forall x : A, p x <-> q x),
  (exists x, p x) <-> (exists x, q x).
Proof.
  firstorder.
Qed.

Lemma all_iff :
  forall A p q (EQ: forall x : A, p x <-> q x),
  (forall x, p x) <-> (forall x, q x).
Proof.
  firstorder.
Qed.

Lemma option_not_none {T} :
  forall x : option T,
  ~ x = None <-> exists v, x = Some v.
Proof.
  intros x. split; intro H1.
  - intuition. destruct x; vauto.
  - intro. desf.
Qed.


(** ** Functions *)

(** Auxiliary results and lemmas on functions. *)

(** Here [update] is the _modification_ of a function [f] at [x] by value [v]. *)

Definition update {A} (f : Z -> A)(x : Z)(v : A) : Z -> A :=
  fun y : Z => if Z.eq_dec x y then v else f y.

Lemma update_apply {A} f x (v : A) :
  (update f x v) x = v.
Proof.
  unfold update.
  destruct (Z.eq_dec x x); intuition omega.
Qed.

Lemma update_idemp {A} f x (v : A) :
  update (update f x v) x v = update f x v.
Proof.
  unfold update.
  extensionality v'.
  desf.
Qed.

Lemma update_eq_dep {A} f g x (v : A) :
  update f x v = update g x v ->
  forall y, x <> y -> f y = g y.
Proof.
  intros H1 y H2.
  unfold update in H1.
  apply equal_f with y in H1.
  desf.
Qed.

Lemma update_idle {A} (f : Z -> A) :
  forall x,
  f = update f x (f x).
Proof.
  intro x.
  unfold update.
  extensionality y.
  desf.
Qed.

Lemma update_idle2 {A} (f : Z -> A) :
  forall (x : Z)(v : A),
  f x = v -> update f x v = f.
Proof.
  intros x v H.
  unfold update.
  extensionality y. desf.
Qed.


(** ** Lists *)

Definition disjoint A (X Y : A -> Prop) :=
  forall x, X x -> Y x -> False.

Definition disjoint_list A (xl yl : list A) :=
  forall x (IN1 : In x xl) (IN2 : In x yl), False.

Definition pred_of_list A (l : list A) (x : A) := In x l.

Coercion pred_of_list : list >-> Funclass.

Lemma disjoint_conv :
  forall A (l1 l2 : list A),
  disjoint l1 l2 -> disjoint_list l1 l2.
Proof.
  done.
Qed.


(** Auxiliary results and lemmas on lists. *)

Fixpoint updatelist {A} (f : Z -> A) (xs : list (Z*A)) : Z -> A :=
  match xs with
    | (x,y)::xs' => updatelist (update f x y) xs'
    | nil => f
  end.

Fixpoint list_zip {A B} (xs : list A) (ys : list B) : list (A * B) :=
  match (xs, ys) with
    | (x::xs', y::ys') => (x, y) :: list_zip xs' ys'
    | _ => nil
  end.

Fixpoint list_zipped {A B} (xs : list A) (ys : list B) (zs : list (A * B)) : Prop :=
  match (xs, ys, zs) with
    | (x::xs', y::ys', (z1, z2)::zs') => x = z1 /\ y = z2 /\ list_zipped xs' ys' zs'
    | (nil, nil, nil) => True
    | _ => False
  end.

Fixpoint list_disj {A} (xs ys : list A) : Prop :=
  match xs with
    | nil => True
    | x::xs' => ~ In x ys /\ list_disj xs' ys
  end.

Lemma in_app {T} :
  forall (xs ys : list T)(x : T),
  In x xs -> In x (xs ++ ys).
Proof.
  intros xs ys x H.
  assert (In x xs \/ In x ys).
  by left.
  by apply in_or_app in H0.
Qed.

Lemma list_member_not_split {T} :
  forall (x : T)(xs1 xs2 : list T),
  ~ In x (xs1 ++ xs2) ->
  ~ In x xs1 /\ ~ In x xs2.
Proof.
  intros x xs1 xs2 H.
  intuition.
Qed.

Lemma remove_In_neq {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall xs x y,
  x <> y ->
  In x xs <-> In x (remove eq_dec y xs).
Proof.
  induction xs; intros x y H1; simpls.
  split; intro H2.
  (* left to right *)
  - destruct H2 as [H2 | H2]; clarify.
    desf; vauto.
    desf. by apply IHxs.
    by apply in_cons, IHxs.
  (* right to left *)
  - desf; vauto.
    right. by apply IHxs in H2.
    simpls.
    destruct H2 as [H2 | H2]; clarify.
    by left. right.
    rewrite <- IHxs in H2; auto.
Qed.

Lemma map_eq_In {T U} :
  forall (xs : list T)(x : T)(f1 f2 : T -> U),
  In x xs ->
  map f1 xs = map f2 xs ->
  f1 x = f2 x.
Proof.
  induction xs; intros x f1 f2 H1 H2; simpls.
  destruct H1 as [H1 | H1]. clarify.
  apply IHxs; auto.
  repeat rewrite <- map_cons in H2.
  desf.
Qed.


(** *** List partitioning *)

(** Properties of the [partition] operation that are not in the standard library. *)

Lemma partition_permut {T} :
  forall (xs ys1 ys2 : list T)(f : T -> bool),
  partition f xs = (ys1, ys2) ->
  Permutation xs (ys1 ++ ys2).
Proof.
  induction xs as [|x xs IH]; intros ys1 ys2 f H1.
  (* base case *)
  - simpls. vauto.
  (* induction case *)
  - simpls. desf; simpls.
    + apply perm_skip. by apply IH with f.
    + transitivity (x :: ys1 ++ l0); [|by list_permutation].
      apply perm_skip. by apply IH with f.
Qed.

Lemma partition_f_left {T} :
  forall (xs ys1 ys2 : list T)(f : T -> bool),
  partition f xs = (ys1, ys2) ->
  forall x : T, In x ys1 -> f x = true.
Proof.
  induction xs as [|x xs IH]; intros ys1 ys2 f H1 y H2.
  (* base case *)
  - simpls. vauto.
  (* induction case *)
  - simpls. desf; simpls; desf; vauto.
    + by apply IH with l ys2.
    + by apply IH with ys1 l0.
Qed.

Lemma partition_f_right {T} :
  forall (xs ys1 ys2 : list T)(f : T -> bool),
  partition f xs = (ys1, ys2) ->
  forall x : T, In x ys2 -> f x = false.
Proof.
  induction xs as [|x xs IH]; intros ys1 ys2 f H1 y H2.
  (* base case *)
  - simpls. vauto.
  (* induction case *)
  - simpls. desf; simpls; desf; vauto.
    + by apply IH with l ys2.
    + by apply IH with ys1 l0.
Qed.

Lemma partition_exists {T} :
  forall (xs : list T)(f : T -> bool),
  exists ys, partition f xs = ys.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f. specialize IH with f.
  destruct IH as ((ys1 & ys2) & H1). simpls. desf.
  (* [f x] is true *)
  - by exists (x :: ys1, ys2).
  (* [f x] is false *)
  - by exists (ys1, x :: ys2).
Qed.

Lemma partition_res {T} :
  forall (xs : list T)(f : T -> bool),
  partition f xs = (fst (partition f xs), snd (partition f xs)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f. simpl. desf.
Qed.


(** *** Lists of natural numbers *)

Open Scope nat_scope.

Fixpoint list_nat_max (xs : list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs' => max x (list_nat_max xs')
  end.

Lemma list_nat_max_app :
  forall xs x,
  list_nat_max (x :: xs) = max x (list_nat_max xs).
Proof.
  induction xs; intro x; simpls.
Qed.

Lemma list_nat_max_tail :
  forall xs x,
  list_nat_max xs <= list_nat_max (x :: xs).
Proof.
  induction xs; intro x; simpls.
  rewrite Max.max_0_r.
  apply Peano.le_0_n.
  apply Nat.le_trans with (max a (max x (list_nat_max xs))).
  by apply Nat.max_le_compat_l.
  rewrite Max.max_assoc.
  rewrite Max.max_comm with a x.
  by rewrite <- Max.max_assoc.
Qed.

Lemma list_nat_max_le_app :
  forall xs x,
  x <= list_nat_max (x :: xs).
Proof.
  induction xs; intro x; simpls.
  by rewrite Max.max_0_r.
  apply Nat.le_trans with (list_nat_max (x :: xs)); simpls.
  apply Nat.max_le_compat_l.
  rewrite <- list_nat_max_app.
  apply list_nat_max_tail.
Qed.

Lemma list_nat_max_In :
  forall xs x,
  In x xs -> x <= list_nat_max xs.
Proof.
  induction xs; intros x H; simpls.
  destruct H as [H | H]. clarify.
  rewrite <- list_nat_max_app.
  apply list_nat_max_le_app.
  apply Nat.le_trans with (list_nat_max xs); auto.
  rewrite <- list_nat_max_app.
  apply list_nat_max_tail.
Qed.

Lemma list_nat_max_In_neg :
  forall xs,
  ~ In ((list_nat_max xs) + 1) xs.
Proof.
  intros xs H.
  apply list_nat_max_In in H.
  apply Nat.nle_succ_diag_l with (n := list_nat_max xs).
  omega.
Qed.

(** Given any list of natural numbers, one can always find a natural number
    that is not in this list. *)

Lemma list_nat_max_notin :
  forall xs : list nat,
  exists x : nat, ~ In x xs.
Proof.
  intro xs. exists ((list_nat_max xs) + 1).
  intro H. by apply list_nat_max_In_neg in H.
Qed.

Close Scope nat_scope.


(** *** Lists of integers *)

Open Scope Z_scope.

Fixpoint list_Z_max (xs : list Z) : Z :=
  match xs with
    | nil => 0
    | x :: xs' => Z.max x (list_Z_max xs')
  end.

Lemma list_Z_max_app :
  forall xs x,
  list_Z_max (x :: xs) = Z.max x (list_Z_max xs).
Proof.
  induction xs; intro x; simpls.
Qed.

Lemma list_Z_max_tail :
  forall xs x,
  list_Z_max xs <= list_Z_max (x :: xs).
Proof.
  induction xs; intro x; simpls.
  apply Z.le_max_r.
  apply Z.le_trans with (Z.max a (Z.max x (list_Z_max xs))).
  by apply Z.max_le_compat_l.
  rewrite Z.max_assoc.
  rewrite Z.max_comm with a x.
  rewrite <- Z.max_assoc.
  reflexivity.
Qed.

Lemma list_Z_max_le_app :
  forall xs x,
  x <= list_Z_max (x :: xs).
Proof.
  induction xs; intro x; simpls.
  apply Z.le_max_l.
  apply Z.le_trans with (list_Z_max (x :: xs)); simpls.
  apply Z.max_le_compat_l.
  rewrite <- list_Z_max_app.
  apply list_Z_max_tail.
Qed.

Lemma list_Z_max_In :
  forall xs x,
  In x xs -> x <= list_Z_max xs.
Proof.
  induction xs; intros x H; simpls.
  destruct H as [H | H]. clarify.
  rewrite <- list_Z_max_app.
  apply list_Z_max_le_app.
  apply Z.le_trans with (list_Z_max xs); auto.
  rewrite <- list_Z_max_app.
  apply list_Z_max_tail.
Qed.

Lemma list_Z_max_In_neg :
  forall xs,
  ~ In ((list_Z_max xs) + 1) xs.
Proof.
  intros xs H.
  apply list_Z_max_In in H.
  apply Z.nle_succ_diag_l with (n := list_Z_max xs).
  omega.
Qed.

(** Given any (finite) list of integers, one can always find an
    integer that is not in this list. *)

Lemma list_Z_max_notin :
  forall xs : list Z,
  exists x : Z, ~ In x xs.
Proof.
  intro xs. exists ((list_Z_max xs) + 1).
  intro H. by apply list_Z_max_In_neg in H.
Qed.

Close Scope Z_scope.


(** *** List removal *)

(** The [removeFirst] operation removes only the _first_ occurrence of a
    given element [x] in a given list [xs]. *)

Section ListRemoval.

Variable T : Type.
Hypothesis eq_dec : forall x y : T, { x = y } + { x <> y }.

Fixpoint removeFirst (x : T)(xs : list T) : list T :=
  match xs with
    | [] => []
    | y :: xs' => if eq_dec x y then xs' else y :: removeFirst x xs'
  end.

Lemma Permutation_moveleft :
  forall (xs : list T)(x : T),
  In x xs -> Permutation xs (x :: removeFirst x xs).
Proof.
  induction xs; intros x H; simpls.
  destruct H as [H | H]. clarify.
  apply perm_skip. destruct (eq_dec x x); vauto.
  destruct (eq_dec x a); vauto.
  transitivity (a :: x :: removeFirst x xs).
  apply perm_skip. by apply IHxs.
  apply perm_swap.
Qed.

End ListRemoval.


(** *** Permutations *)

(** Different results on permutations on certain substructures and operations on lists. *)

Lemma map_permut {T U} :
  forall (xs ys : list T)(f : T -> U),
  Permutation xs ys ->
  Permutation (map f xs) (map f ys).
Proof.
  intros xs ys f PERM.
  induction PERM; simpls.
  by apply perm_skip.
  by apply perm_swap.
  by transitivity (map f l').
Qed.

Add Parametric Morphism {T U} : (@map T U)
  with signature eq ==> @Permutation T ==> @Permutation U
    as map_permut_mor.
Proof.
  intros f xs ys H.
  by apply map_permut.
Qed.


(** ** Finite sets *)

(** *** Auxiliary results *)

(** Some results that are not present in the ListSet library. *)

Lemma set_In_permutation {T}:
  forall (xs ys : set T)(e : T),
  Permutation xs ys -> set_In e xs -> set_In e ys.
Proof.
  intros xs ys e H.
  induction H; simpls; desf; intuition vauto.
Qed.

Add Parametric Morphism {T} : (@set_In T)
  with signature eq ==> (@Permutation T) ==> iff
    as set_In_permut_mor.
Proof.
  intros e xs ys H1. split; intro H2.
  by apply set_In_permutation with xs.
  apply set_In_permutation with ys; auto.
Qed.

Lemma set_remove_permutation {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs ys : set T)(e : T),
  Permutation xs ys ->
  Permutation (set_remove eq_dec e xs) (set_remove eq_dec e ys).
Proof.
  intros xs ys e H.
  induction H; simpls; desf; intuition vauto.
Qed.

Hint Resolve set_remove_permutation.

Add Parametric Morphism {T} : (@set_remove T)
  with signature eq ==> eq ==> (@Permutation T) ==> (@Permutation T)
    as set_remove_permut_mor.
Proof.
  intros eq_dec e xs ys H.
  by apply set_remove_permutation.
Qed.

Lemma set_In_remove {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall xs x y,
  x <> y -> set_In x (set_remove eq_dec y xs) <-> set_In x xs.
Proof.
  induction xs; ins; desf; simpls; intuition vauto.
  right. by apply IHxs with y.
  right. by apply IHxs.
Qed.

Lemma set_remove_swap {T} (eq_dec : forall x y : T, { x = y } + { x <> y }):
  forall xs x y,
  set_remove eq_dec x (set_remove eq_dec y xs) =
  set_remove eq_dec y (set_remove eq_dec x xs).
Proof.
  induction xs; ins; simpls; desf; simpls; desf; intuition vauto.
  by rewrite IHxs.
Qed.

Lemma set_remove_cons {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs : set T)(x y : T),
  x <> y -> y :: set_remove eq_dec x xs = set_remove eq_dec x (y :: xs).
Proof.
  induction xs; ins; desf.
Qed.


(** *** Subset *)

Definition subset {T} (X Y : set T) : Prop :=
  forall e : T, set_In e X -> set_In e Y.

Instance subset_refl {T} :
  Reflexive (@subset T).
Proof.
  by repeat red.
Qed.

Hint Resolve subset_refl.

Instance subset_trans {T} :
  Transitive (@subset T).
Proof.
  red. intros ???????.
  by apply H0, H.
Qed.

Section Subset.

Variable T : Type.
Hypothesis eq_dec : forall x y : T, { x = y } + { x <> y }.

Lemma subset_add :
  forall (e : T)(X : set T),
  subset [e] (set_add eq_dec e X).
Proof.
  red. red. ins. desf.
  by apply set_add_intro2.
Qed.

Lemma subset_add_mono :
  forall (e : T)(X : set T),
  subset X (set_add eq_dec e X).
Proof.
  red. ins. by apply set_add_intro1.
Qed.

Lemma subset_union_mono_l :
  forall (X Y : set T),
  subset X (set_union eq_dec X Y).
Proof.
  red. red. ins.
  by apply set_union_intro1.
Qed.

Lemma subset_union_mono_r :
  forall (X Y : set T),
  subset X (set_union eq_dec Y X).
Proof.
  red. red. ins.
  by apply set_union_intro2.
Qed.

Lemma subset_union_l :
  forall (X1 X2 Y : set T),
  subset X1 X2 -> subset (set_union eq_dec X1 Y) (set_union eq_dec X2 Y).
Proof.
  intros X1 X2 Y H1 e H2.
  apply set_union_intro.
  apply set_union_elim in H2. des.
  left. by apply H1.
  by right.
Qed.

Lemma subset_union_r :
  forall (X Y1 Y2 : set T),
  subset Y1 Y2 -> subset (set_union eq_dec X Y1) (set_union eq_dec X Y2).
Proof.
  intros X1 X2 Y H1 e H2.
  apply set_union_intro.
  apply set_union_elim in H2. des.
  by left.
  right. by apply H1.
Qed.

End Subset.

Add Parametric Morphism {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) : (set_union eq_dec)
  with signature (@subset T) ==> (@subset T) ==> (@subset T)
    as set_union_subset_mor.
Proof.
  intros X1 Y1 H1 X2 Y2 H2.
  transitivity (set_union eq_dec Y1 X2).
  by apply subset_union_l.
  by apply subset_union_r.
Qed.


(** *** Sublists *)

(** A slightly different definition than [subset]; here elements are allowed to
    occur multiple times in the specified lists. *)

(** TODO: prove antisymmetry. *)

Section Sublist.

Variable T : Type.
Hypothesis eq_dec : forall x y : T, { x = y } + { x <> y }.

Fixpoint sublist (xs ys : set T) : Prop :=
  match xs with
    | nil => True
    | x :: xs' => set_In x ys /\ sublist xs' (set_remove eq_dec x ys)
  end.

Lemma sublist_In :
  forall (xs ys : set T)(x : T),
  sublist xs ys -> set_In x xs -> set_In x ys.
Proof.
  induction xs; ins; simpls; desf; intuition vauto.
  assert (x = a \/ x <> a). tauto. desf.
  apply IHxs with (x := x) in H1; vauto.
  by rewrite set_In_remove in H1.
Qed.

Lemma sublist_cons :
  forall (xs ys : set T)(x : T),
  sublist xs (x :: ys) <-> sublist (set_remove eq_dec x xs) ys.
Proof.
  induction xs; ins; simpls; desf; simpls;
    desf; intuition vauto; by apply IHxs.
Qed.

Lemma sublist_nil :
  forall xs : set T,
  sublist xs nil -> xs = nil.
Proof.
  induction xs; ins; simpls; desf.
Qed.

Lemma sublist_remove_In :
  forall (ys xs : set T)(x : T),
  set_In x ys ->
  sublist xs (set_remove eq_dec x ys) <-> sublist (x :: xs) ys.
Proof.
  induction ys; ins; simpls; desf; intuition vauto.
Qed.

Lemma sublist_remove :
  forall (xs ys : set T)(x : T),
  sublist xs ys -> sublist (set_remove eq_dec x xs) (set_remove eq_dec x ys).
Proof.
  induction xs, ys; ins; simpls; desf; simpls; desf; intuition vauto;
    try by apply IHxs.
  - by rewrite <- sublist_cons.
  - right. rewrite set_In_remove; auto.
  - repeat rewrite set_remove_cons; auto.
    rewrite set_remove_swap.
    apply IHxs. by rewrite <- set_remove_cons.
Qed.

Instance sublist_refl :
  Reflexive sublist.
Proof.
  red. induction x; simpls; intuition vauto; desf.
Qed.

Hint Resolve sublist_refl.

Instance sublist_trans :
  Transitive sublist.
Proof.
  red. induction x, y; simpls; desf; intuition vauto.
  - by apply IHx with y.
  - by apply IHx with y.
  - rewrite <- set_In_remove; vauto.
    apply sublist_In with y; vauto.
  - apply IHx with (t :: set_remove eq_dec a y); auto.
    rewrite set_remove_cons; vauto.
    apply sublist_remove.
    by apply sublist_remove_In.
Qed.

Lemma sublist_permutation_r :
  forall xs ys1 ys2 : set T,
  Permutation ys1 ys2 -> sublist xs ys1 -> sublist xs ys2.
Proof.
  induction xs; ins; intuition vauto.
  by rewrite <- H.
  apply IHxs with (set_remove eq_dec a ys1); vauto.
  by apply set_remove_permutation.
Qed.

Lemma sublist_permutation_l :
  forall xs1 xs2 : set T,
  Permutation xs1 xs2 ->
  forall ys, sublist xs1 ys -> sublist xs2 ys.
Proof.
  intros xs1 xs2 H.
  induction H; ins; simpls; desf; intuition vauto.
  - by apply IHPermutation.
  - assert (x = y \/ x <> y). tauto. desf.
    by rewrite set_In_remove in H0.
  - assert (x = y \/ x <> y). tauto. desf.
    rewrite set_In_remove. done. intro. by apply H2.
  - by rewrite set_remove_swap.
  - by apply IHPermutation2, IHPermutation1.
Qed.

Add Parametric Morphism : sublist
  with signature (@Permutation T) ==> (@Permutation T) ==> iff
    as sublist_permut_mor.
Proof.
  intros xs1 ys1 H1 xs2 ys2 H2. split; intro H3.
  apply sublist_permutation_l with xs1; vauto.
  apply sublist_permutation_r with xs2; vauto.
  apply sublist_permutation_l with ys1. by symmetry.
  apply sublist_permutation_r with ys2; auto.
Qed.

Lemma sublist_permutation :
  forall xs ys,
  Permutation xs ys -> sublist xs ys.
Proof.
  intros xs ys H.
  destruct H; simpls; desf; simpls; desf; intuition vauto.
  by rewrite H.
  by rewrite H, H0.
Qed.

Hint Resolve sublist_permutation.

End Sublist.


(** ** Finite maps *)

(** A list of pairs is a _finite map_ if there are no duplicates among the left elements *)

Definition fmap_dom {T U} (xs : list (T * U)) : list T :=
  fst (split xs).

Definition fmap {T U} (xs : list (T * U)) : Prop :=
  NoDup (fmap_dom xs).

Lemma fmap_dom_cons {T U} :
  forall (xs : list (T * U))(x : T * U),
  fmap_dom (x :: xs) = fst x :: fmap_dom xs.
Proof.
  induction xs; intro x; simpls;
    unfold fmap_dom; simpls; desf.
Qed.

Lemma fmap_dom_In {T U} :
  forall (xs : list (T * U))(x : T * U),
  In x xs -> In (fst x) (fmap_dom xs).
Proof.
  induction xs; intros x H; simpls.
  destruct H as [H | H]. clarify.
  rewrite fmap_dom_cons.
  by apply in_eq.
  rewrite fmap_dom_cons.
  by apply in_cons, IHxs.
Qed.


(** The following definition determines whether a list of pairs is
    _projected_ onto a given mapping. *)

Definition projected {T U} (xs : list (T * U))(f : T -> U) : Prop :=
  forall x : T * U, In x xs -> f (fst x) = snd x.
