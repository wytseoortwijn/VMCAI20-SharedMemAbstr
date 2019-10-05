Require Import Assertions.
Require Import Dynamics.
Require Import HahnBase.
Require Import Heap.
Require Import List.
Require Import ListSet.
Require Import Nat.
Require Import Permissions.
Require Import Permutation.
Require Import PermutationTactic.
Require Import Prerequisites.
Require Import ProcessMap.
Require Import Process.
Require Import Statics.
Require Import Soundness.
Require Import QArith.
Require Import Qcanon.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.

Set Implicit Arguments.


(** * Derived proof rules *)

(** This section contains some composite commands and corresponding
    proof derivations from the proof rules of Soundness.v. *)


(** ** Atomic read/fetch *)

Definition Cfetch {T} (X : Var)(E : Expr) : Cmd T := Catomic (Cread X E).

Lemma cfetch_user {T} : forall X E, cmd_user (@Cfetch T X E).
Proof. ins. Qed.
Lemma cfetch_basic {T} : forall X E, cmd_basic (@Cfetch T X E).
Proof. ins. Qed.

Theorem rule_fetch (env : ProcEnv) :
  forall X R E1 E2 A1 A2 A3 t q,
  ~ In X (expr_fv E1) ->
  ~ In X (expr_fv E2) ->
  ~ assn_fv R X ->
  assn_entails (Astar A1 R) (Astar (assn_subst X E2 A2) (Apointsto t q E1 E2)) ->
  assn_entails (Astar A2 (Apointsto t q E1 E2)) (Astar A3 R) ->
  csl env False R A1 (Cfetch X E1) A3.
Proof.
  intros X R E1 E2 A1 A2 A3 t q IN1 IN2 IN3 ENT1 ENT2.
  unfold Cfetch. apply rule_atom.
    apply rule_conseq with
    (A1' := Astar (assn_subst X E2 A2) (Apointsto t q E1 E2))
    (A2' := Astar A2 (Apointsto t q E1 E2)); auto.
  apply rule_lookup; auto.
Qed.


(** ** Compare-and-swap *)

(** The following composite command resembles an atomic CAS: the value [E3] is written
    to the heap location [E1], but only if that heap location contains the value [E2]. The
    old value at [E1] is returned (actually, written to [X]). *)

Definition Ccas {T} (X : Var)(E1 E2 E3 : Expr) : Cmd T :=
  Catomic (Cseq (Cread X E1) (Cite (Beq (Evar X) E2) (Cwrite E1 E3) Cskip)).

Print Beq.

Theorem rule_cas (env : ProcEnv) :
  forall X E1 E1' E2 E3 R A1 A1' A2,
  ~ In X (expr_fv E1) ->
  ~ In X (expr_fv E1') ->
  ~ assn_fv R X ->
  assn_entails (Astar A1 R) (Astar (assn_subst X E1' A1') (Apointsto PTTstd perm_full E1 E1')) ->
  assn_entails (Astar A1' (Adisj (Astar (Apointsto PTTstd perm_full E1 E3) (Aplain (Beq E1' E2))) (Astar (Apointsto PTTstd perm_full E1 E2) (Aplain (Bnot (Beq E1' E2)))))) (Astar A2 R) ->
  csl env False R A1 (Ccas X E1 E2 E3) A2.
Proof.
  intros X E1 E1' E2 E3 R A1 A1' A2 IN1 IN2 IN3 H1 H2.
  unfold Ccas. apply rule_atom.

  pose (A1'' := Aplain (Beq (Evar X) E1')).

  assert (H3 : assn_entails (Astar A1 R) (Astar (assn_subst X E1' (Astar A1' A1''))(Apointsto PTTstd perm_full E1 E1'))). {
    rewrite H1. simpl (assn_subst X E1' (Astar A1' A1'')).
    destruct (Z.eq_dec X X) as [_|?]; vauto.
    rewrite expr_subst_pres; auto. apply assn_star_add_r.
    rewrite assn_star_true at 1. apply assn_star_add_l.
    apply assn_plain_tauto. }

  apply rule_conseq with
    (A1' := Astar (assn_subst X E1' (Astar A1' A1'')) (Apointsto PTTstd perm_full E1 E1'))
    (A2' := Astar A1' (Adisj (Astar (Apointsto PTTstd perm_full E1 E3) (Aplain (Beq E1' E2))) (Astar (Apointsto PTTstd perm_full E1 E2) (Aplain (Bnot (Beq E1' E2)))))); auto.

  apply rule_seq with (Astar (Astar A1' A1'') (Apointsto PTTstd perm_full E1 E1')).
  (* lookup *)
  - by apply rule_lookup.
  (* if-then-else *)
  - apply rule_ite.
    (* true branch *)
    + subst A1''. rewrite assn_star_disj.
      apply rule_disj_weaken.




