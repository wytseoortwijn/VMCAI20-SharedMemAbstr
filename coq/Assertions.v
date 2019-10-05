Require Import Dynamics.
Require Import HahnBase.
Require Import Heap.
Require Import List.
Require Import Permissions.
Require Import Permutation.
Require Import PermutationTactic.
Require Import Prerequisites.
Require Import Process.
Require Import ProcessMap.
Require Import QArith.
Require Import Qcanon.
Require Import Statics.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.


(** * Assertions *)

(** This document discusses the assertions of our program logic, in particular
    their statics, dynamics, logical entailment, and several proof rules of our logic. *)

(** ** Statics *)

(** Below the statics of the assertions is given. *)

Inductive PointsToType := PTTstd | PTTproc | PTTact.

Add Search Blacklist "PointsToType_rect".
Add Search Blacklist "PointsToType_ind".
Add Search Blacklist "PointsToType_rec".

Inductive Assn :=
  | Aplain(B:BoolExpr)
  | Aex(lambda:Val->Assn)
  | Adisj(A1 A2:Assn)
  | Astar(A1 A2:Assn)
  | Awand(A1 A2:Assn)
  | Apointsto(t:PointsToType)(q:Qc)(E1 E2:Expr)
  | Aproc(x:Var)(q:Qc)(p:ProcLabel)(P:Proc)(xs:list ProcVar)(f:ProcVar -> Expr).

Add Search Blacklist "Assn_rect".
Add Search Blacklist "Assn_ind".
Add Search Blacklist "Assn_rec".

Definition Atrue : Assn := Aplain (Bconst true).
Definition Afalse : Assn := Aplain (Bconst false).

Definition Apointsto_procact (q : Qc)(E1 E2 : Expr) : Assn :=
  if Qc_eq_dec q perm_full
  then Apointsto PTTact q E1 E2
  else Apointsto PTTproc q E1 E2.

Fixpoint Aiter (xs : list Assn) : Assn :=
  match xs with
    | nil => Atrue
    | A :: xs' => Astar A (Aiter xs')
  end.

Definition pointsto_iter {T} (xs : list T)(F : T -> Qc)(f1 f2 : T -> Expr)(t : PointsToType) : list Assn :=
  map (fun x : T => Apointsto t (F x) (f1 x) (f2 x)) xs.

Definition pointsto_iter_procact {T} (xs : list T)(F : T -> Qc)(f1 f2 : T -> Expr) : list Assn :=
	map (fun x : T => Apointsto_procact (F x) (f1 x) (f2 x)) xs.

Lemma pointsto_iter_cons {T} :
  forall (xs : list T)(x : T) F f1 f2 t,
  pointsto_iter (x :: xs) F f1 f2 t =
  Apointsto t (F x) (f1 x) (f2 x) :: pointsto_iter xs F f1 f2 t.
Proof.
  ins.
Qed.

Lemma pointsto_iter_app {T} :
  forall (xs ys : list T)(fq : T -> Qc)(f1 f2 : T -> Expr)(t : PointsToType),
  pointsto_iter xs fq f1 f2 t ++ pointsto_iter ys fq f1 f2 t =
  pointsto_iter (xs ++ ys) fq f1 f2 t.
Proof.
  intros xs ys fq f1 f2 t. unfold pointsto_iter.
  by rewrite map_app.
Qed.

Lemma pointsto_iter_procact_app {T} :
  forall (xs ys : list T)(fq : T -> Qc)(f1 f2 : T -> Expr),
  pointsto_iter_procact xs fq f1 f2 ++ pointsto_iter_procact ys fq f1 f2 =
  pointsto_iter_procact (xs ++ ys) fq f1 f2.
Proof.
  intros xs ys fq f1 f2. unfold pointsto_iter_procact.
  by rewrite map_app.
Qed.

Lemma pointsto_iter_ext_in {T} :
  forall (xs : list T)(fq fq' : T -> Qc)(f1 f1' f2 f2' : T -> Expr) t,
    (forall x : T, In x xs -> fq x = fq' x) ->
    (forall x : T, In x xs -> f1 x = f1' x) ->
    (forall x : T, In x xs -> f2 x = f2' x) ->
  pointsto_iter xs fq f1 f2 t = pointsto_iter xs fq' f1' f2' t.
Proof.
  intros xs fq fq' f1 f1' f2 f2' t H1 H2 H3.
  unfold pointsto_iter. apply map_ext_in.
  intros x H4. rewrite H1, H2, H3; vauto.
Qed.

Lemma pointsto_iter_procact_ext_in {T} :
  forall (xs : list T)(fq fq' : T -> Qc)(f1 f1' f2 f2' : T -> Expr),
    (forall x : T, In x xs -> fq x = fq' x) ->
    (forall x : T, In x xs -> f1 x = f1' x) ->
    (forall x : T, In x xs -> f2 x = f2' x) ->
  pointsto_iter_procact xs fq f1 f2 = pointsto_iter_procact xs fq' f1' f2'.
Proof.
  intros xs fq fq' f1 f1' f2 f2' H1 H2 H3.
  unfold pointsto_iter_procact. apply map_ext_in.
  intros x H4. rewrite H1, H2, H3; vauto.
Qed.


(** *** Free variables *)

Fixpoint assn_fv (A : Assn)(x : Var) : Prop :=
  match A with
    | Aplain B => In x (bexpr_fv B)
    | Aex lambda => exists v : Val, assn_fv (lambda v) x
    | Adisj A1 A2
    | Astar A1 A2
    | Awand A1 A2 => assn_fv A1 x \/ assn_fv A2 x
    | Apointsto _ _ E1 E2 => In x (expr_fv E1) \/ In x (expr_fv E2)
    | Aproc y _ _ _ _ f => x = y \/ expr_map_fv f x
  end.

Lemma assn_fv_iter :
  forall (xs : list Assn)(x : Var),
  assn_fv (Aiter xs) x <->
  exists A, In A xs /\ assn_fv A x.
Proof.
  induction xs as [|A xs IH]; intro x.
  (* base case *)
  - split; intro H; desf.
  (* induction case *)
  - split; intro H.
    (* left to right *)
    + simpl in H. destruct H as [H | H].
      * exists A. split; vauto.
      * rewrite IH in H. destruct H as (A' & H1 & H2).
        exists A'. split; auto. by apply in_cons.
    (* right to left *)
    + destruct H as (A' & H1 & H2).
      simpls. destruct H1 as [H1 | H1]; vauto.
      right. rewrite IH. exists A'. split; vauto.
Qed.

Lemma assn_fv_pointsto_iter {T} :
  forall (xs : list T) F f1 f2 t x,
  assn_fv (Aiter (pointsto_iter xs F f1 f2 t)) x <->
  exists e : T, In e xs /\ (In x (expr_fv (f1 e)) \/ In x (expr_fv (f2 e))).
Proof.
  intros xs F f1 f2 t x. split; intro H.
  (* left to right *)
  - rewrite assn_fv_iter in H.
    destruct H as (A & H1 & H2).
    unfold pointsto_iter in H1.
    rewrite in_map_iff in H1.
    destruct H1 as (e & H1 & H3). clarify.
    simpl in H2. exists e. intuition.
  (* right to left *)
  - destruct H as (e & H1 & H2).
    rewrite assn_fv_iter.
    exists (Apointsto t (F e) (f1 e) (f2 e)). split; vauto.
    unfold pointsto_iter. rewrite in_map_iff.
    exists e. intuition.
Qed.


(** *** Substitution *)

Fixpoint assn_subst (x : Var)(E : Expr)(A : Assn) : Assn :=
  match A with
    | Aplain B => Aplain (bexpr_subst x E B)
    | Aex lambda => Aex (fun v : Val => assn_subst x E (lambda v))
    | Adisj A1 A2 => Adisj (assn_subst x E A1) (assn_subst x E A2)
    | Astar A1 A2 => Astar (assn_subst x E A1) (assn_subst x E A2)
    | Awand A1 A2 => Awand (assn_subst x E A1) (assn_subst x E A2)
    | Apointsto t q E1 E2 => Apointsto t q (expr_subst x E E1) (expr_subst x E E2)
    | Aproc X q p P xs f => Aproc X q p P xs (expr_subst_map x E f)
  end.

Lemma assn_subst_pres :
  forall A x E,
  ~ assn_fv A x -> assn_subst x E A = A.
Proof.
  induction A; intros y E H1; simpls; vauto.
  (* non-spatial assertions *)
  - rewrite bexpr_subst_pres; auto.
  (* existential quantifiers *)
  - cut (lambda = fun v => assn_subst y E (lambda v)).
    intro H2. by rewrite <- H2.
    extensionality v'. rewrite H; auto.
    intros H2. apply H1. by exists v'.
  (* disjunction *)
  - rewrite IHA1, IHA2; auto.
  (* separating conjunction *)
  - rewrite IHA1, IHA2; auto.
  (* magic wand *)
  - rewrite IHA1, IHA2; auto.
  (* points-to ownership predicates *)
  - repeat rewrite expr_subst_pres; auto; intro; apply H.
  (* process ownership predicates *)
  - rewrite expr_subst_pres_map; vauto.
    intro H2. destruct H2 as (t & H2).
    apply H1. right. by exists t.
Qed.

Definition Aexists (x : Var)(A : Assn) : Assn :=
  Aex (fun v : Val => assn_subst x (Econst v) A).


(** ** Dynamics *)

(** The _satisfaction relation_ [assn_sat] defines the meaning of assertions. *)

Fixpoint assn_sat (ph : PermHeap)(pm : ProcMap)(s g : Store)(A:Assn) : Prop :=
  match A with
    (* non-spatial assertions *)
    | Aplain B => bexpr_denot B s = true
    (* existential quantifier *)
    | Aex lambda => exists v : Val, assn_sat ph pm s g (lambda v)
    (* disjunction *)
    | Adisj A1 A2 =>
        assn_sat ph pm s g A1 \/ assn_sat ph pm s g A2
    (* separating conjunction *)
    | Astar A1 A2 =>
        exists ph1 ph2,
          permheap_disj ph1 ph2 /\
          permheap_add ph1 ph2 = ph /\
        exists pm1 pm2,
          procmap_disj pm1 pm2 /\
          procmap_eq (procmap_add pm1 pm2) pm /\
          assn_sat ph1 pm1 s g A1 /\
          assn_sat ph2 pm2 s g A2
    (* magic wand *)
    | Awand A1 A2 =>
        forall ph' pm',
        permheap_disj ph ph' ->
        procmap_disj pm pm' ->
        assn_sat ph' pm' s g A1 ->
        assn_sat (permheap_add ph ph') (procmap_add pm pm') s g A2
    (* standard points-to predicate *)
    | Apointsto PTTstd q E1 E2 =>
        let l := expr_denot E1 s in
        let v := expr_denot E2 s in
        phc_le (PHCstd q v) (ph l)
    (* process points-to predicate *)
    | Apointsto PTTproc q E1 E2 =>
        let l := expr_denot E1 s in
        let v := expr_denot E2 s in
        phc_le (PHCproc q v) (ph l)
    (* action points-to predicate *)
    | Apointsto PTTact q E1 E2 =>
        let l := expr_denot E1 s in
        let v := expr_denot E2 s in
        exists v', phc_le (PHCact q v v') (ph l)
    (* process ownership predicate *)
    | Aproc x q p P xs f =>
        let pmv := PMelem q p P xs (expr_denot_map f s) in
        exists pmv', pmv_disj pmv pmv' /\ pmv_eq (pm (g x)) (pmv_add pmv pmv')
  end.

Lemma assn_sat_procmap_eq :
  forall A ph pm1 pm2 s g,
  procmap_eq pm1 pm2 ->
  assn_sat ph pm1 s g A ->
  assn_sat ph pm2 s g A.
Proof.
  induction A; intros ph pm1 pm2 s g H1 H2; auto.
  (* existential quantifiers *)
  - simpl in H2. destruct H2 as (v & H2).
    exists v. by apply H with pm1.
  (* disjunction *)
  - simpls. destruct H2 as [H2 | H2].
    left. by apply IHA1 with pm1.
    right. by apply IHA2 with pm1.
  (* separating conjunction *)
  - simpls.
    destruct H2 as (ph1 & ph2 & D1 & H2 & pm3 & pm4 & D2 & H3 & SAT1 & SAT2).
    exists ph1, ph2. intuition.
    exists pm3, pm4. intuition.
    by rewrite <- H1.
  (* magic wand *)
  - simpls. intros ph' pm' H3 H4 H5.
    apply IHA2 with (procmap_add pm1 pm').
    by rewrite H1.
    apply H2; auto. by rewrite H1.
  (* process ownership predicate *)
  - unfold assn_sat in *.
    destruct H2 as (pmv & H2 & H3).
    exists pmv. intuition.
    rewrite <- H3. intuition.
Qed.

Add Parametric Morphism : assn_sat
  with signature eq ==> procmap_eq ==> eq ==> eq ==> eq ==> iff
    as assn_sat_procmap_mor.
Proof.
  intros ph pm1 pm2 H1 s g A. split; intro H2.
  apply assn_sat_procmap_eq with pm1; auto.
  apply assn_sat_procmap_eq with pm2; auto.
Qed.

Lemma assn_sat_subst :
  forall A ph pm s g x E,
  assn_sat ph pm s g (assn_subst x E A) <->
  assn_sat ph pm (update s x (expr_denot E s)) g A.
Proof.
  induction A; intros ph pm s g y E'; auto.
  (* non-spatial assertions *)
  - split; intro H; simpls.
    + by rewrite <- bexpr_denot_subst.
    + by rewrite bexpr_denot_subst.
  (* existential quantifiers *)
  - split; intro H1; simpls.
    + destruct H1 as (v & H1).
      exists v. by apply H.
    + destruct H1 as (v & H1).
      exists v. by apply <- H.
  (* disjunction *)
  - split; intro H; simpls.
    + destruct H as [H | H].
      left. by rewrite <- IHA1.
      right. by rewrite <- IHA2.
    + destruct H as [H | H].
      left. by rewrite IHA1.
      right. by rewrite IHA2.
  (* separating conjunction *)
  - split; intro H; simpls.
    + destruct H as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
      exists ph1, ph2. intuition.
      exists pm1, pm2. intuition.
      by apply IHA1. by apply IHA2.
    + destruct H as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
      exists ph1, ph2. intuition.
      exists pm1, pm2. intuition.
      by apply <- IHA1. by apply <- IHA2.
  (* magic wands *)
  - split; intro H; simpls.
    + intros ph' pm' D1 D2 SAT.
      apply IHA2, H; auto.
      by apply IHA1.
    + intros ph' pm' D1 D2 SAT.
      apply IHA2, H; auto.
      by apply IHA1.
  (* points-to ownership predicates *)
  - split; intro H.
    + simpl. repeat rewrite <- expr_denot_subst in *. vauto.
    + simpl. repeat rewrite expr_denot_subst in *. vauto.
  (* process ownership predicates *)
  - split; intro H2.
    + destruct H2 as (pmv & H2 & H3). exists pmv.
      rewrite <- expr_denot_subst_map in *. vauto.
    + destruct H2 as (pmv & H2 & H3). exists pmv.
      rewrite expr_denot_subst_map in *. vauto.
Qed.

Lemma assn_sat_agree :
  forall A ph pm s1 s2 g,
    (forall x, assn_fv A x -> s1 x = s2 x) ->
  assn_sat ph pm s1 g A <->
  assn_sat ph pm s2 g A.
Proof.
  induction A; intros ph pm s1 s2 g H1.
  (* non-spatial assertions *)
  - split; intro H2; simpls.
    + rewrite <- bexpr_agree with (s1 := s1); vauto.
    + rewrite bexpr_agree with (s2 := s2); vauto.
  (* existential quantifiers *)
  - split; intro H2; simpls.
    + destruct H2 as (v & H2).
      exists v. rewrite <- H with (s1 := s1); auto.
      intros x H3. apply H1.
      by exists v.
    + destruct H2 as (v & H2).
      exists v. rewrite H with (s2 := s2); auto.
      intros x H3. apply H1.
      by exists v.
  (* disjunction *)
  - split; intro H2; simpls.
    + destruct H2 as [H2 | H2].
      left. rewrite <- IHA1 with (s1 := s1); auto.
      right. rewrite <- IHA2 with (s1 := s1); auto.
    + destruct H2 as [H2 | H2].
      left. rewrite IHA1 with (s2 := s2); auto.
      right. rewrite IHA2 with (s2 := s2); auto.
  (* separating conjunction *)
  - split; intro H2; simpls.
    + destruct H2 as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
      exists ph1, ph2. intuition.
      exists pm1, pm2. intuition.
      rewrite <- IHA1 with (s1 := s1); auto.
      rewrite <- IHA2 with (s1 := s1); auto.
    + destruct H2 as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
      exists ph1, ph2. intuition.
      exists pm1, pm2. intuition.
      rewrite IHA1 with (s2 := s2); auto.
      rewrite IHA2 with (s2 := s2); auto.
  (* magic wand *)
  - split; intro H2; simpls.
    + intros ph' pm' H3 H4 H5.
      rewrite <- IHA2 with (s1 := s1); auto.
      apply H2; auto.
      rewrite IHA1 with (s2 := s2); auto.
    + intros ph' pm' H3 H4 H5.
      rewrite IHA2 with (s2 := s2); auto.
      apply H2; auto.
      rewrite <- IHA1 with (s1 := s1); auto.
  (* points-to ownership predicates *)
  - split; intro H2; unfold assn_sat in H2.
    + rewrite expr_agree with (s2 := s2) in H2; auto.
      destruct t; unfold assn_sat.
      * rewrite <- expr_agree with (E := E1)(s1 := s1); auto.
        red. intros x H3. apply H1. simpl. by left.
      * rewrite <- expr_agree with (E := E1)(s1 := s1); auto.
        red. intros x H3. apply H1. simpl. by left.
      * rewrite <- expr_agree with (E := E1)(s1 := s1); auto.
        red. intros x H3. apply H1. simpl. by left.
      * red. intros x H3. apply H1. simpl. by right.
    + rewrite <- expr_agree with (s1 := s1) in H2; auto.
      destruct t; unfold assn_sat.
      * rewrite expr_agree with (E := E1)(s2 := s2); auto.
        red. intros x H3. apply H1. simpl. by left.
      * rewrite expr_agree with (E := E1)(s2 := s2); auto.
        red. intros x H3. apply H1. simpl. by left.
      * rewrite expr_agree with (E := E1)(s2 := s2); auto.
        red. intros x H3. apply H1. simpl. by left.
      * red. intros x H3. apply H1. simpl. by right.
  (* process ownership predicates *)
  - split; intro H2; unfold assn_sat in *.
    + destruct H2 as (pmv & H2 & H3).
      rewrite <- expr_map_agree with (s3 := s1); vauto.
      intros y H4. destruct H4 as (z & H4).
      apply H1. right. by exists z.
    + destruct H2 as (pmv & H2 & H3).
      rewrite expr_map_agree with (s4 := s2); vauto.
      intros y H4. destruct H4 as (z & H4).
      apply H1. right. by exists z.
Qed.

Lemma assn_sat_ghost_agree :
  forall A ph pm s g1 g2,
    (forall x, assn_fv A x -> g1 x = g2 x) ->
  assn_sat ph pm s g1 A <->
  assn_sat ph pm s g2 A.
Proof.
  induction A; intros ph pm s1 g1 g2 H1.
  (* non-spatial assertions *)
  - split; intro H2; simpls.
  (* existential quantifiers *)
  - split; intro H2; simpls.
    + destruct H2 as (v & H2). exists v.
      rewrite <- H with (g1 := g1); vauto.
      intros x H3. apply H1. by exists v.
    + destruct H2 as (v & H2). exists v.
      rewrite H with (g2 := g2); vauto.
      intros x H3. apply H1. by exists v.
  (* disjunction *)
  - split; intro H2; simpls.
    + destruct H2 as [H2 | H2].
      left. rewrite <- IHA1 with (g1 := g1); auto.
      right. rewrite <- IHA2 with (g1 := g1); auto.
    + destruct H2 as [H2 | H2].
      left. rewrite IHA1 with (g2 := g2); auto.
      right. rewrite IHA2 with (g2 := g2); auto.
  (* separating conjunction *)
  - split; intro H2; simpls.
    + destruct H2 as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
      exists ph1, ph2. intuition.
      exists pm1, pm2. intuition.
      rewrite <- IHA1 with (g1 := g1); auto.
      rewrite <- IHA2 with (g1 := g1); auto.
    + destruct H2 as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
      exists ph1, ph2. intuition.
      exists pm1, pm2. intuition.
      rewrite IHA1 with (g2 := g2); auto.
      rewrite IHA2 with (g2 := g2); auto.
  (* magic wand *)
  - split; intro H2; simpls.
    + intros ph' pm' H3 H4 H5.
      rewrite <- IHA2 with (g1 := g1); auto.
      apply H2; auto.
      rewrite IHA1 with (g2 := g2); auto.
    + intros ph' pm' H3 H4 H5.
      rewrite IHA2 with (g2 := g2); auto.
      apply H2; auto.
      rewrite <- IHA1 with (g1 := g1); auto.
  (* points-to ownership predicates *)
  - split; intro H2; simpls.
  (* process ownership predicates *)
  - split; intro H2; unfold assn_sat in *.
    + destruct H2 as (pmv & H2 & H3).
      exists pmv. split; vauto.
      rewrite <- H3. rewrite H1; auto.
      simpl. by left.
    + destruct H2 as (pmv & H2 & H3).
      exists pmv. split; vauto.
      rewrite <- H3. rewrite H1; auto.
      simpl. by left.
Qed.

Lemma assn_sat_upd :
  forall A ph pm s g x v,
  ~ assn_fv A x ->
  assn_sat ph pm (update s x v) g A <-> assn_sat ph pm s g A.
Proof.
  intros A ph pm s g x v H1.
  split; intro H2.
  (* left to right *)
  - rewrite assn_sat_agree with (s2 := update s x v); auto.
    intros y H3. unfold update.
    destruct (Z.eq_dec x y); vauto.
  (* right to left *)
  - rewrite <- assn_sat_agree with (s1 := s); auto.
    intros y H3. unfold update.
    destruct (Z.eq_dec x y); vauto.
Qed.

Lemma assn_sat_upd_ghost :
  forall A ph pm s g x v,
  ~ assn_fv A x ->
  assn_sat ph pm s (update g x v) A <-> assn_sat ph pm s g A.
Proof.
  intros A ph pm s g x v H1.
  split; intro H2.
  (* left to right *)
  - rewrite assn_sat_ghost_agree with (g2 := update g x v); auto.
    intros y H3. unfold update.
    destruct (Z.eq_dec x y); vauto.
  (* right to left *)
  - rewrite <- assn_sat_ghost_agree with (g1 := g); auto.
    intros y H3. unfold update.
    destruct (Z.eq_dec x y); vauto.
Qed.

Lemma assn_sat_weaken :
  forall A ph1 ph2 pm1 pm2 s g,
  permheap_disj ph1 ph2 ->
  procmap_disj pm1 pm2 ->
  assn_sat ph1 pm1 s g A ->
  assn_sat (permheap_add ph1 ph2) (procmap_add pm1 pm2) s g A.
Proof.
  induction A; intros ph1 ph2 pm1 pm2 s g H1 H2 H3; auto.
  (* existential quantifiers *)
  - simpls. destruct H3 as (v & H3).
    exists v. by apply H.
  (* disjunction *)
  - simpls. destruct H3 as [H3 | H3].
    left. by apply IHA1.
    right. by apply IHA2.
  (* separating conjunction *)
  - simpls.
    destruct H3 as (ph3 & ph4 & D1 & H4 & pm3 & pm4 & D2 & H5 & SAT1 & SAT2).
    clarify. exists ph3, (permheap_add ph4 ph2). intuition.
    by apply permheap_disj_assoc_l.
    exists pm3, (procmap_add pm4 pm2). intuition.
    apply procmap_disj_assoc_l; auto.
    by rewrite H5.
    rewrite <- procmap_add_assoc.
    by rewrite H5.
    apply IHA2; auto.
    by apply permheap_disj_add_l with ph3.
    apply procmap_disj_add_l with pm3; auto.
    by rewrite H5.
  (* magic wand *)
  - simpls. intros ph' pm' H4 H5 H6.
    rewrite permheap_add_assoc, procmap_add_assoc.
    apply H3.
    by apply permheap_disj_assoc_l.
    by apply procmap_disj_assoc_l.
    rewrite permheap_add_comm, procmap_add_comm.
    apply IHA1; auto.
    apply permheap_disj_add_r with ph1.
    by symmetry. symmetry.
    by rewrite permheap_add_comm.
    apply procmap_disj_add_r with pm1.
    by symmetry. symmetry.
    by rewrite procmap_add_comm.
  (* points-to ownership predicates *)
  - unfold assn_sat in *. destruct t.
    + rewrite <- permheap_add_cell.
      apply phc_le_weaken; vauto.
    + rewrite <- permheap_add_cell.
      apply phc_le_weaken; vauto.
    + destruct H3 as (v & H3).
      exists v. rewrite <- permheap_add_cell.
      apply phc_le_weaken; vauto.
  (* process ownership predicate *)
  - unfold assn_sat in *.
    destruct H3 as (pmv & H3 & H4).
    exists (pmv_add pmv (pm2 (g x))). split.
    + apply pmv_disj_assoc_l; auto.
      rewrite <- H4. intuition.
    + rewrite <- pmv_add_assoc, <- H4.
      by rewrite <- procmap_add_pmv.
Qed.

Lemma assn_sat_iter_permut :
  forall xs ys,
  Permutation xs ys ->
  forall ph pm s g,
  assn_sat ph pm s g (Aiter xs) ->
  assn_sat ph pm s g (Aiter ys).
Proof.
  intros xs ys PERM.
  induction PERM; intros ph pm s g SAT; simpls.
  - destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
  - destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT).
    destruct SAT as (ph3 & ph4 & D3 & H3 & pm3 & pm4 & D4 & H4 & SAT3 & SAT4).
    clarify.
    exists ph3, (permheap_add ph1 ph4). intuition.
    { (* disjointness of [ph3] and [ph1 + ph4] *)
    apply permheap_disj_assoc_l. symmetry.
    by apply permheap_disj_add_r with ph4.
    rewrite permheap_add_comm.
    by apply permheap_disj_assoc_r. }
    { (* equality of [ph3 + ph1 + ph4] and [ph1 + ph3 + ph4] *)
    rewrite <- permheap_add_assoc.
    rewrite permheap_add_comm with ph3 ph1.
    by rewrite permheap_add_assoc. }
    exists pm3, (procmap_add pm1 pm4). intuition.
    { (* disjointness of [pm3] and [pm1 + pm4] *)
    apply procmap_disj_assoc_l. symmetry.
    apply procmap_disj_add_r with pm4; auto.
    by rewrite H4. rewrite procmap_add_comm.
    apply procmap_disj_assoc_r; auto.
    by rewrite H4. }
    { (* equality of [pm3 + pm1 + pm4] and [pm1 + pm3 + pm4] *)
    rewrite <- procmap_add_assoc.
    rewrite procmap_add_comm with (pm1 := pm3)(pm2 := pm1).
    rewrite procmap_add_assoc.
    by rewrite <- H2, <- H4. }
    exists ph1, ph4. intuition.
    apply permheap_disj_add_r with ph3; auto.
    by rewrite permheap_add_comm.
    exists pm1, pm4. intuition.
    apply procmap_disj_add_r with pm3; auto.
    by rewrite procmap_add_comm, H4.
  - by apply IHPERM2, IHPERM1.
Qed.

(** The satisfiability of points-to predicates is independent of the process map. *)

Lemma assn_sat_pointsto_indep :
  forall ph pm1 pm2 s g t q E1 E2,
  assn_sat ph pm1 s g (Apointsto t q E1 E2) ->
  assn_sat ph pm2 s g (Apointsto t q E1 E2).
Proof.
  intros ph pm1 pm2 s g t q E1 E2 SAT.
  unfold assn_sat in *. desf.
Qed.


(** ** Logical consequence *)

(** The relation [assn_entails] defines _semantic consequence_ of two assertions.
    That is, [A1] is a semantic consequence of [A2] if there is no model
    that distinguishes them. *)

Definition assn_entails (A1 A2 : Assn) : Prop :=
  forall ph pm s g,
    permheap_valid ph ->
    procmap_valid pm ->
    assn_sat ph pm s g A1 ->
    assn_sat ph pm s g A2.

Definition assn_entails_rev (A1 A2 : Assn) : Prop := assn_entails A2 A1.

Definition assn_equiv (A1 A2 : Assn) : Prop :=
  assn_entails A1 A2 /\ assn_entails A2 A1.

Notation "A1 ⊢ A2" := (assn_entails A1 A2) (only printing, at level 80).
Notation "A1 ⊣ A2" := (assn_entails_rev A1 A2) (only printing, at level 80).
Notation "A1 ⊣⊢ A2" := (assn_equiv A1 A2) (only printing, at level 80).

Instance assn_entails_refl : Reflexive assn_entails.
Proof. intro. red. intuition. Qed.
Instance assn_entails_trans : Transitive assn_entails.
Proof. unfold assn_entails. intuition. Qed.
Instance assn_entails_rev_refl : Reflexive assn_entails_rev.
Proof. intro. red. intuition. Qed.
Instance assn_entails_rev_trans : Transitive assn_entails_rev.
Proof. unfold assn_entails_rev. intros ?????. by transitivity y. Qed.
Instance assn_equiv_refl : Reflexive assn_equiv.
Proof. red. ins. split; vauto. Qed.
Instance assn_equiv_symm : Symmetric assn_equiv.
Proof. red. intros A1 A2 (H1&H2). split; auto. Qed.
Instance assn_equiv_trans : Transitive assn_equiv.
Proof. red. intros A1 A2 A3 (H1&H2) (H3&H4). split; by transitivity A2. Qed.
Instance assn_equiv_eq : Equivalence assn_equiv.
Proof. split; intuition. Qed.

Hint Resolve assn_entails_refl assn_entails_rev_refl assn_equiv_refl.

Lemma assn_entails_flip :
  forall A1 A2, assn_entails A1 A2 <-> assn_entails_rev A2 A1.
Proof. ins. Qed.

(** *** Congruence *)

(** Logical consequence is a _congruence_ with respect to all connectives of the proof logic. *)

Add Parametric Morphism : Adisj
  with signature assn_entails ==> assn_entails ==> assn_entails
    as assn_disj_entails_mor.
Proof.
  intros A1 A1' ENT1 A2 A2' ENT2.
  red. intros ph pm s g Vph Vpm SAT. simpls.
  destruct SAT as [SAT | SAT].
  left. apply ENT1; auto.
  right. apply ENT2; auto.
Qed.

Add Parametric Morphism : Adisj
  with signature assn_equiv ==> assn_equiv ==> assn_entails
    as assn_disj_equiv_ent_mor.
Proof. intros A1 A2 (H1&_) A3 A4 (H2&_). by rewrite H1,H2. Qed.

Add Parametric Morphism : Adisj
  with signature assn_equiv ==> assn_equiv ==> assn_equiv
    as assn_disj_equiv_mor.
Proof.
  intros A1 A2 (H1&H2) A3 A4 (H3&H4). split.
  - by rewrite H1, H3.
  - by rewrite H2, H4.
Qed.

Add Parametric Morphism : Astar
  with signature assn_entails ==> assn_entails ==> assn_entails
    as assn_star_entails_mor.
Proof.
  intros A1 A1' ENT1 A2 A2' ENT2.
  red. intros ph pm s g Vph Vpm SAT. simpls.
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  exists ph1, ph2. intuition.
  exists pm1, pm2. intuition.
  apply ENT1; auto.
  by apply permheap_disj_valid_l in D1.
  by apply procmap_disj_valid_l in D2.
  apply ENT2; auto.
  by apply permheap_disj_valid_r in D1.
  by apply procmap_disj_valid_r in D2.
Qed.

Add Parametric Morphism : Astar
  with signature assn_equiv ==> assn_equiv ==> assn_entails
    as assn_star_equiv_ent_mor.
Proof. intros A1 A2 (H1&_) A3 A4 (H2&_). by rewrite H1,H2. Qed.

Add Parametric Morphism : Astar
  with signature assn_equiv ==> assn_equiv ==> assn_equiv
    as assn_star_equiv_mor.
Proof.
  intros A1 A2 (H1&H2) A3 A4 (H3&H4). split.
  - by rewrite H1,H3.
  - by rewrite H2,H4.
Qed.

Add Parametric Morphism : Awand
  with signature assn_entails_rev ==> assn_entails ==> assn_entails
    as assn_wand_entails_mor.
Proof.
  intros A1 A1' ENT1 A2 A2' ENT2.
  red. intros ph pm s g Vph Vpm WAND. simpls.
  intros ph' pm' D1 D2 SAT1.
  apply ENT2; auto.
  apply WAND; auto.
  apply ENT1; auto.
  by apply permheap_disj_valid_r in D1.
  by apply procmap_disj_valid_r in D2.
Qed.

Add Parametric Morphism : Awand
  with signature assn_equiv ==> assn_equiv ==> assn_equiv
    as assn_wand_equiv_mor.
Proof.
  intros A1 A2 (H1&H2) A3 A4 (H3&H4). split.
  - rewrite assn_entails_flip in H2. by rewrite H2,H3.
  - rewrite assn_entails_flip in H1. by rewrite H1,H4.
Qed.


(** *** Weakening rule *)

Lemma assn_sat_star_combine :
  forall ph1 ph2 pm1 pm2 s g A1 A2,
  permheap_disj ph1 ph2 ->
  procmap_disj pm1 pm2 ->
  assn_sat ph1 pm1 s g A1 ->
  assn_sat ph2 pm2 s g A2 ->
  assn_sat (permheap_add ph1 ph2) (procmap_add pm1 pm2) s g (Astar A1 A2).
Proof.
  intros ph1 ph2 pm1 pm2 s g A1 A2 D1 D2 H1 H2.
  exists ph1, ph2. repeat split; auto.
  exists pm1, pm2. repeat split; auto.
Qed.

Lemma assn_sat_star_weaken :
  forall ph pm s g A1 A2,
  assn_sat ph pm s g (Astar A1 A2) ->
  assn_sat ph pm s g A1.
Proof.
  intros ph pm s g A1 A2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  rewrite <- H1, <- H2. by apply assn_sat_weaken.
Qed.

(** The following rule shows that our separation logic is _intuitionistic_. *)

Theorem assn_weaken :
  forall A1 A2, assn_entails (Astar A1 A2) A1.
Proof.
  intros A1 A2 ph pm s g H1 H2 H3.
  by apply assn_sat_star_weaken with A2.
Qed.


(** *** Separating conjunction *)

(** Soundness of the axioms of _associativity_ and _commutativity_. *)

Lemma assn_sat_star_assoc_l :
  forall ph pm s g A1 A2 A3,
  assn_sat ph pm s g (Astar A1 (Astar A2 A3)) ->
  assn_sat ph pm s g (Astar (Astar A1 A2) A3).
Proof.
  intros ph pm s g A1 A2 A3 SAT.
  destruct SAT as (ph1 & ph1' & D1 & H1 & pm1 & pm1' & D2 & H2 & SAT1 & SAT2).
  destruct SAT2 as (ph2 & ph3 & D3 & H3 & pm2 & pm3 & D4 & H4 & SAT2 & SAT3).
  exists (permheap_add ph1 ph2), ph3. repeat split; vauto.
  { (* [ph1 + ph2] is disjoint with [ph3] *)
  by apply permheap_disj_assoc_r. }
  exists (procmap_add pm1 pm2), pm3. repeat split; vauto.
  { (* [pm1 + pm2] is disjoint with [pm3] *)
  apply procmap_disj_assoc_r; auto. by rewrite H4. }
  { (* [pm1 + pm2 + pm3] equals [pm] *)
  rewrite <- H2, <- H4. by rewrite procmap_add_assoc. }
  exists ph1, ph2. repeat split; vauto.
  { (* [ph1] is disjoint with [ph2] *)
  apply permheap_disj_add_r with ph3; auto. }
  exists pm1, pm2. repeat split; vauto.
  { (* [pm1] is disjoint with [pm2] *)
  apply procmap_disj_add_r with pm3; auto. by rewrite H4. }
Qed.

Theorem assn_star_assoc_l :
  forall A1 A2 A3,
  assn_entails (Astar A1 (Astar A2 A3)) (Astar (Astar A1 A2) A3).
Proof.
  intros A1 A2 A3 ph pm s g H1 H2 H3.
  by apply assn_sat_star_assoc_l.
Qed.

Lemma assn_sat_star_assoc_r :
  forall ph pm s g A1 A2 A3,
  assn_sat ph pm s g (Astar (Astar A1 A2) A3) ->
  assn_sat ph pm s g (Astar A1 (Astar A2 A3)).
Proof.
  intros ph pm s g A1 A2 A3 SAT.
  destruct SAT as (ph1' & ph3 & D1 & H1 & pm1' & pm3 & D2 & H2 & SAT1 & SAT2).
  destruct SAT1 as (ph1 & ph2 & D3 & H3 & pm1 & pm2 & D4 & H4 & SAT1 & SAT3).
  exists ph1, (permheap_add ph2 ph3). repeat split; vauto.
  { (* [ph1] is disjoint with [ph2 + ph3] *)
  by apply permheap_disj_assoc_l. }
   exists pm1, (procmap_add pm2 pm3). repeat split; vauto.
  { (* [pm1] is disjoint with [pm2 + pm3] *)
  apply procmap_disj_assoc_l; auto. by rewrite H4. }
  { (* [pm1 + pm2 + pm3] equals [pm] *)
  rewrite <- H2, <- H4. by rewrite procmap_add_assoc. }
  exists ph2, ph3. repeat split; vauto.
  { (* [ph2] is disjoint with [ph3] *)
  apply permheap_disj_add_l with ph1; auto. }
  exists pm2, pm3. repeat split; vauto.
  { (* [pm2] is disjoint with [pm3] *)
  apply procmap_disj_add_l with pm1; auto. by rewrite H4. }
Qed.

Theorem assn_star_assoc_r :
  forall A1 A2 A3,
  assn_entails (Astar (Astar A1 A2) A3) (Astar A1 (Astar A2 A3)).
Proof.
  intros A1 A2 A3 ph pm s g H1 H2 H3.
  by apply assn_sat_star_assoc_r.
Qed.

Theorem assn_star_assoc :
  forall A1 A2 A3, assn_equiv (Astar (Astar A1 A2) A3) (Astar A1 (Astar A2 A3)).
Proof. ins. split; [apply assn_star_assoc_r|apply assn_star_assoc_l]. Qed.

Lemma assn_sat_star_comm :
  forall ph pm s g A1 A2,
  assn_sat ph pm s g (Astar A1 A2) ->
  assn_sat ph pm s g (Astar A2 A1).
Proof.
  intros ph pm s g A1 A2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  exists ph2, ph1. repeat split; auto.
  by rewrite permheap_add_comm.
  exists pm2, pm1. repeat split; auto.
  by rewrite procmap_add_comm.
Qed.

Theorem assn_star_comm :
  forall A1 A2, assn_entails (Astar A1 A2) (Astar A2 A1).
Proof.
  intros A1 A2 ph pm s g H1 H2 H3.
  by apply assn_sat_star_comm.
Qed.

Theorem assn_star_comm_equiv :
  forall A1 A2, assn_equiv (Astar A1 A2) (Astar A2 A1).
Proof. ins. split; by apply assn_star_comm. Qed.

Corollary assn_weaken_r :
  forall A1 A2, assn_entails (Astar A1 A2) A2.
Proof.
  intros A1 A2. transitivity (Astar A2 A1).
  apply assn_star_comm. apply assn_weaken.
Qed.

Corollary assn_weaken_l :
  forall A1 A2, assn_entails (Astar A1 A2) A1.
Proof.
  intros A1 A2. rewrite assn_star_comm. by apply assn_weaken_r.
Qed.

Lemma assn_sat_star_true :
  forall ph pm s g A,
  permheap_valid ph ->
  procmap_valid pm ->
  assn_sat ph pm s g A ->
  assn_sat ph pm s g (Astar A Atrue).
Proof.
  intros ph pm s g A V1 V2 SAT.
  exists ph, permheap_iden. repeat split; auto.
  { (* [ph + iden] equals [ph] *)
  by rewrite permheap_add_iden_l. }
  exists pm, procmap_iden. repeat split; auto.
  { (* [pm + iden] equals [pm] *)
  by rewrite procmap_add_iden_l. }
Qed.

Theorem assn_star_true :
  forall A, assn_entails A (Astar A Atrue).
Proof.
  intros A ph pm s g V1 V2 SAT.
  by apply assn_sat_star_true.
Qed.

Lemma assn_sat_star_swap_l :
  forall ph pm s g A1 A2 A3,
  assn_sat ph pm s g (Astar A1 (Astar A2 A3)) ->
  assn_sat ph pm s g (Astar A2 (Astar A1 A3)).
Proof.
  intros ph pm s g A1 A2 A3 SAT.
  apply assn_sat_star_assoc_r.
  apply assn_sat_star_assoc_l in SAT.
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  exists ph1, ph2. repeat split; vauto.
  exists pm1, pm2. repeat split; vauto.
  by apply assn_sat_star_comm.
Qed.

Lemma assn_star_swap_l :
  forall A1 A2 A3,
  assn_entails (Astar A1 (Astar A2 A3)) (Astar A2 (Astar A1 A3)).
Proof.
  intros A1 A2 A3. rewrite assn_star_assoc_l.
  rewrite assn_star_comm with (A1 := A1)(A2 := A2).
  by rewrite assn_star_assoc_r.
Qed.

Lemma assn_sat_star_swap_r :
  forall ph pm s g A1 A2 A3,
  assn_sat ph pm s g (Astar (Astar A1 A2) A3) ->
  assn_sat ph pm s g (Astar (Astar A1 A3) A2).
Proof.
  intros ph pm s g A1 A2 A3 SAT.
  apply assn_sat_star_assoc_l.
  apply assn_sat_star_assoc_r in SAT.
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  exists ph1, ph2. repeat split; vauto.
  exists pm1, pm2. repeat split; vauto.
  by apply assn_sat_star_comm.
Qed.

Lemma assn_star_swap_r :
  forall A1 A2 A3,
  assn_entails (Astar (Astar A1 A2) A3) (Astar (Astar A1 A3) A2).
Proof.
  intros A1 A2 A3. rewrite assn_star_assoc_r.
  rewrite assn_star_comm with (A1 := A2)(A2 := A3).
  by rewrite assn_star_assoc_l.
Qed.

Theorem assn_star_add_l :
  forall A1 A2 A3,
  assn_entails A2 A3 -> assn_entails (Astar A1 A2) (Astar A1 A3).
Proof. intros ??? ENT. by rewrite ENT. Qed.

Theorem assn_star_add_r :
  forall A1 A2 A3,
  assn_entails A2 A3 -> assn_entails (Astar A2 A1) (Astar A3 A1).
Proof. intros ??? ENT. by rewrite ENT. Qed.

Lemma assn_star_disj_l :
  forall A1 A2 A3,
  assn_entails (Astar A1 (Adisj A2 A3)) (Adisj (Astar A1 A2) (Astar A1 A3)).
Proof.
  intros A1 A2 A3 ph pm s g V1 V2 (ph1&ph2&D1&EQ1&pm1&pm2&D2&EQ2&SAT1&SAT2).
  destruct SAT2 as [SAT2|SAT2].
  - left. exists ph1,ph2. intuition. exists pm1,pm2. intuition.
  - right. exists ph1,ph2. intuition. exists pm1,pm2. intuition.
Qed.

Lemma assn_star_disj_r :
  forall A1 A2 A3,
  assn_entails (Adisj (Astar A1 A2) (Astar A1 A3)) (Astar A1 (Adisj A2 A3)).
Proof.
  intros A1 A2 A3 ph pm s g V1 V2 [SAT|SAT];
    destruct SAT as (ph1&ph2&D1&EQ1&pm1&pm2&D2&EQ2&SAT1&SAT2).
  - exists ph1,ph2. intuition. exists pm1,pm2. intuition. by left.
  - exists ph1,ph2. intuition. exists pm1,pm2. intuition. by right.
Qed.

Lemma assn_star_disj :
  forall A1 A2 A3,
  assn_equiv (Astar A1 (Adisj A2 A3)) (Adisj (Astar A1 A2) (Astar A1 A3)).
Proof. ins. split; [by apply assn_star_disj_l|by apply assn_star_disj_r]. Qed.


(** *** Iterated separating conjunction *)

Theorem assn_iter_permut :
  forall xs ys, Permutation xs ys -> assn_entails (Aiter xs) (Aiter ys).
Proof.
  intros xs ys H. red. intros ph pm s g Vph Vpm SAT.
  by apply assn_sat_iter_permut with xs.
Qed.

Add Parametric Morphism : Aiter
  with signature @Permutation Assn ==> assn_entails
    as assn_iter_permut_mor.
Proof. ins. by apply assn_iter_permut. Qed.

Lemma assn_sat_iter_cons_l :
  forall ph pm s g A xs,
  assn_sat ph pm s g (Astar A (Aiter xs)) ->
  assn_sat ph pm s g (Aiter (A :: xs)).
Proof. intuition vauto. Qed.

Theorem assn_iter_cons_l :
  forall A xs, assn_entails (Astar A (Aiter xs)) (Aiter (A :: xs)).
Proof. intuition vauto. Qed.

Lemma assn_sat_iter_cons_r :
  forall ph pm s g A xs,
  assn_sat ph pm s g (Aiter (A :: xs)) ->
  assn_sat ph pm s g (Astar A (Aiter xs)).
Proof. intuition vauto. Qed.

Theorem assn_iter_cons_r :
  forall A xs, assn_entails (Aiter (A :: xs)) (Astar A (Aiter xs)).
Proof. intuition vauto. Qed.

Lemma assn_sat_iter_add_l :
  forall (xs ys : list Assn) ph pm s g,
  assn_sat ph pm s g (Astar (Aiter xs) (Aiter ys)) ->
  assn_sat ph pm s g (Aiter (xs ++ ys)).
Proof.
  induction xs as [|A xs IH]; intros ys ph pm s g SAT.
  - simpl (Aiter []) in SAT. rewrite app_nil_l.
    by apply assn_sat_star_comm, assn_sat_star_weaken in SAT.
  - simpl (Aiter (A :: xs)) in SAT.
    replace ((A :: xs) ++ ys) with (A :: (xs ++ ys)); auto.
    apply assn_sat_iter_cons_l. apply assn_sat_star_assoc_r in SAT.
    destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. repeat split; vauto.
    by apply IH.
Qed.

Theorem assn_iter_add_l :
  forall xs ys, assn_entails (Astar (Aiter xs) (Aiter ys)) (Aiter (xs ++ ys)).
Proof.
  intros xs ys ph pm s g V1 V2 SAT.
  by apply assn_sat_iter_add_l.
Qed.

Lemma assn_sat_iter_add_r :
  forall (xs ys : list Assn) ph pm s g,
  permheap_valid ph ->
  procmap_valid pm ->
  assn_sat ph pm s g (Aiter (xs ++ ys)) ->
  assn_sat ph pm s g (Astar (Aiter xs) (Aiter ys)).
Proof.
  induction xs as [|A xs IH]; intros ys ph pm s g V1 V2 SAT.
  - simpl (Aiter []). rewrite app_nil_l in SAT.
    apply assn_sat_star_comm. by apply assn_sat_star_true.
  - simpl (Aiter (A :: xs)).
    replace ((A :: xs) ++ ys) with (A :: (xs ++ ys)) in SAT; auto.
    apply assn_sat_iter_cons_r in SAT. apply assn_sat_star_assoc_l.
    destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. repeat split; vauto.
    apply IH; vauto.
    { (* [ph2] is valid *)
    by apply permheap_disj_valid_r in D1. }
    { (* [pm2] is valid *)
    by apply procmap_disj_valid_r in D2. }
Qed.

Theorem assn_iter_add_r :
  forall xs ys, assn_entails (Aiter (xs ++ ys)) (Astar (Aiter xs) (Aiter ys)).
Proof.
  induction xs; intro ys; simpls.
  rewrite <- assn_star_comm.
  by rewrite <- assn_star_true.
  rewrite <- assn_star_assoc_l.
  by rewrite <- IHxs.
Qed.

Lemma assn_sat_iter_star_l :
  forall ph pm s g A1 A2 (xs : list Assn),
  assn_sat ph pm s g (Aiter (Astar A1 A2 :: xs)) ->
  assn_sat ph pm s g (Aiter (A1 :: A2 :: xs)).
Proof.
  intros ph pm s g A1 A2 xs SAT.
  simpl (Aiter (A1 :: A2 :: xs)).
  by apply assn_sat_star_assoc_r.
Qed.

Theorem assn_iter_star_l :
  forall A1 A2 xs,
  assn_entails (Aiter (Astar A1 A2 :: xs)) (Aiter (A1 :: A2 :: xs)).
Proof.
  intros A1 A2 xs. simpls.
  by rewrite assn_star_assoc_r.
Qed.

Lemma assn_sat_iter_star_r :
  forall ph pm s g A1 A2 (xs : list Assn),
  assn_sat ph pm s g (Aiter (A1 :: A2 :: xs)) ->
  assn_sat ph pm s g (Aiter (Astar A1 A2 :: xs)).
Proof.
  intros ph pm s g A1 A2 xs SAT.
  simpl (Aiter (A1 :: A2 :: xs)) in SAT.
  by apply assn_sat_star_assoc_l.
Qed.

Theorem assn_iter_star_r :
  forall A1 A2 xs,
  assn_entails (Aiter (A1 :: A2 :: xs)) (Aiter (Astar A1 A2 :: xs)).
Proof.
  intros A1 A2 xs. simpls.
  by rewrite assn_star_assoc_l.
Qed.

Lemma assn_sat_iter_weaken :
  forall ph pm s g A (xs : list Assn),
  assn_sat ph pm s g (Aiter (A :: xs)) ->
  assn_sat ph pm s g (Aiter xs).
Proof.
  intros ph pm s g A xs SAT.
  simpl (Aiter (A :: xs)) in SAT.
  apply assn_sat_star_weaken with A.
  by apply assn_sat_star_comm.
Qed.

Corollary assn_iter_weaken :
  forall A xs,
  assn_entails (Aiter (A :: xs)) (Aiter xs).
Proof.
  intros A xs.
  rewrite assn_iter_cons_r.
  rewrite assn_star_comm.
  by rewrite assn_weaken.
Qed.

Lemma assn_sat_iter_In_l {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs : list T) ph pm s g (f : T -> Assn)(x : T),
  In x xs ->
  assn_sat ph pm s g (Aiter (map f xs)) ->
  assn_sat ph pm s g (Astar (f x) (Aiter (map f (removeFirst eq_dec x xs)))).
Proof.
  intros xs ph pm s g f x H1 SAT.
  apply Permutation_moveleft with (eq_dec := eq_dec) in H1.
  apply assn_sat_iter_permut with (ys := map f (x :: removeFirst eq_dec x xs)) in SAT; auto.
  by apply Permutation_map.
Qed.

Lemma assn_iter_In_l {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs : list T)(f : T -> Assn)(x : T),
  In x xs ->
  assn_entails (Aiter (map f xs)) (Astar (f x) (Aiter (map f (removeFirst eq_dec x xs)))).
Proof.
  intros xs f x H1 ph pm s g V1 V2 SAT.
  by apply assn_sat_iter_In_l.
Qed.

Lemma assn_sat_iter_In_r {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs : list T) ph pm s g (f : T -> Assn)(x : T),
  In x xs ->
  assn_sat ph pm s g (Astar (f x) (Aiter (map f (removeFirst eq_dec x xs)))) ->
  assn_sat ph pm s g (Aiter (map f xs)).
Proof.
  intros xs ph pm s g f x H1 SAT.
  apply Permutation_moveleft with (eq_dec := eq_dec) in H1.
  apply assn_sat_iter_cons_l in SAT.
  apply assn_sat_iter_permut with (ys := map f xs) in SAT; auto.
  rewrite <- map_cons. apply Permutation_map. by symmetry.
Qed.

Lemma assn_iter_In_r {T} (eq_dec : forall x y : T, { x = y } + { x <> y }) :
  forall (xs : list T)(f : T -> Assn)(x : T),
  In x xs ->
  assn_entails (Astar (f x) (Aiter (map f (removeFirst eq_dec x xs)))) (Aiter (map f xs)).
Proof.
  intros xs f x H1 ph pm s g V1 V2 SAT.
  by apply assn_sat_iter_In_r in SAT.
Qed.

Lemma assn_sat_pointsto_iter_permut {T} :
  forall (xs ys : list T) ph pm s g (fq : T -> Qc)(f1 f2 : T -> Expr) t,
  Permutation xs ys ->
  assn_sat ph pm s g (Aiter (pointsto_iter xs fq f1 f2 t)) ->
  assn_sat ph pm s g (Aiter (pointsto_iter ys fq f1 f2 t)).
Proof.
  intros xs ys ph pm s g fq f1 f2 t H1 SAT.
  apply assn_sat_iter_permut with (pointsto_iter xs fq f1 f2 t); auto.
  apply map_permut_mor; auto.
Qed.

Lemma assn_sat_procact_iter_permut {T} :
  forall (xs ys : list T) ph pm s g (fq : T -> Qc)(f1 f2 : T -> Expr),
  Permutation xs ys ->
  assn_sat ph pm s g (Aiter (pointsto_iter_procact xs fq f1 f2)) ->
  assn_sat ph pm s g (Aiter (pointsto_iter_procact ys fq f1 f2)).
Proof.
  intros xs ys ph pm s g fq f1 f2 H1 SAT.
  apply assn_sat_iter_permut with (pointsto_iter_procact xs fq f1 f2); auto.
  apply map_permut_mor; auto.
Qed.


(** *** Plain assertions *)

(** _Introduction_ and _elimination_ rules for plain assertions. *)

Theorem assn_true_intro :
  forall A, assn_entails A Atrue.
Proof.
  red. simpls.
Qed.

(* ex falso quodlibet *)
Theorem assn_false_elim :
  forall A1 A2,
  assn_entails A1 Afalse ->
  assn_entails A1 A2.
Proof.
  unfold assn_entails.
  intros A1 A2 H1 ph pm s g H2 H3 H4.
  apply H1 in H4; vauto.
Qed.

Lemma assn_plain_tauto :
  forall E,
  assn_entails (Aplain (Beq E E)) Atrue /\
  assn_entails Atrue (Aplain (Beq E E)).
Proof.
  intros E. split.
  - red. ins.
  - red. ins. desf.
Qed.


(** *** Existential quantifiers *)

(** _Introduction_ rule for existential quantification. *)

Theorem assn_exists_intro :
  forall A1 A2 x v,
  assn_entails A1 (assn_subst x (Econst v) A2) ->
  assn_entails A1 (Aexists x A2).
Proof.
  intros A1 A2 x v H ph pm s g H1 H2 H3.
  exists v. by apply H.
Qed.


(** *** Disjunction *)

(** Standard elimination rules for disjunction. *)

Lemma assn_sat_elim_l :
  forall ph pm s g A1 A2,
  assn_sat ph pm s g A1 ->
  assn_sat ph pm s g (Adisj A1 A2).
Proof.
  intros ph pm s g A1 A2 SAT. simpl. by left.
Qed.

Lemma assn_sat_elim_r :
  forall ph pm s g A1 A2,
  assn_sat ph pm s g A2 ->
  assn_sat ph pm s g (Adisj A1 A2).
Proof.
  intros ph pm s g A1 A2 SAT. simpl. by right.
Qed.

Theorem assn_disj_elim_l :
  forall A A1 A2,
  assn_entails A A1 ->
  assn_entails A (Adisj A1 A2).
Proof.
  intros A A1 A2 H ph pm s g V1 V2 SAT.
  by apply assn_sat_elim_l, H.
Qed.

Theorem assn_disj_elim_r :
  forall A A1 A2,
  assn_entails A A2 ->
  assn_entails A (Adisj A1 A2).
Proof.
  intros A A1 A2 H ph pm s g V1 V2 SAT.
  by apply assn_sat_elim_r, H.
Qed.

Lemma assn_disj_idemp :
  forall A,
  assn_entails A (Adisj A A) /\ assn_entails (Adisj A A) A.
Proof.
  intro A. split; ins; vauto. red. ins. desf.
Qed.


(** *** Magic wand *)

(** _Introduction_ and _elimination_ rules for the magic wand. *)

Theorem assn_wand_intro :
  forall A1 A2 A3,
  assn_entails (Astar A1 A2) A3 ->
  assn_entails A1 (Awand A2 A3).
Proof.
  intros A1 A2 A3 H1 ph pm s g H2 H3 H4 ph' pm' H5 H6 H7.
  apply H1; auto.
  exists ph, ph'. intuition.
  exists pm, pm'. intuition.
Qed.

Theorem assn_wand_elim :
  forall A1 A2 A A',
  assn_entails A1 (Awand A A') ->
  assn_entails A2 A ->
  assn_entails (Astar A1 A2) A'.
Proof.
  intros A1 A2 A A' H1 H2 ph pm s g H3 H4 H5.
  simpls. desf. rewrite <- H7.
  apply H1; auto.
  by apply permheap_disj_valid_l in H5.
  by apply procmap_disj_valid_l in H6.
  apply H2; auto.
  by apply permheap_disj_valid_r in H5.
  by apply procmap_disj_valid_r in H6.
Qed.


(** *** Points-to ownership predicates *)

Lemma assn_pointsto_full :
  forall ph pm s g t E1 E2,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto t perm_full E1 E2) ->
  phc_full (ph (expr_denot E1 s)).
Proof.
  intros ph pm s g t E1 E2 H1 SAT.
  destruct t.
  (* standard points-to predicate *)
  - unfold assn_sat in SAT.
    apply phc_le_full_eq in SAT; vauto.
    rewrite <- SAT. vauto.
  (* process points-to predicate *)
  - unfold assn_sat in SAT.
    apply phc_le_full_eq in SAT; vauto.
    rewrite <- SAT. vauto.
  (* standard points-to predicate *)
  - unfold assn_sat in SAT.
    destruct SAT as (v' & SAT).
    apply phc_le_full_eq in SAT; vauto.
    rewrite <- SAT. vauto.
Qed.

Lemma pointsto_iter_perm_full {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr)(l : Loc) ph pm s g t,
    (forall x : T, In x xs -> fq x = perm_full) ->
  assn_sat ph pm s g (Aiter (pointsto_iter xs fq f1 f2 t)) ->
  In l (map (expr_denot_map f1 s) xs) ->
  phc_full (ph l).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros fq f1 f2 l ph pm s g t H1 SAT H2.
  destruct SAT as (ph1 & ph2 & D1 & H3 & pm1 & pm2 & D2 & H4 & SAT1 & SAT2).
  rewrite map_cons in H2. simpl in H2. destruct H2 as [H2 | H2].
  (* [l] equals the head of [xs] *)
  - rewrite H1 in SAT1; vauto.
    apply assn_pointsto_full in SAT1.
    + apply phc_full_add; vauto.
    + by apply permheap_disj_valid_l in D1.
  (* [l] is in the tail of [xs] *)
  - apply IH with (l := l) in SAT2; vauto.
    + apply phc_full_add; auto.
    + intros y H5. apply H1. vauto.
Qed.

(** Heap ownership predicates of different types can not coexist if they target
    the same heap location. *)

Lemma assn_pointsto_diff :
  forall q1 q2 E1 E2 t1 t2,
  t1 <> t2 ->
  assn_entails (Astar (Apointsto t1 q1 E1 E2) (Apointsto t2 q2 E1 E2)) Afalse.
Proof.
  intros q1 q2 E1 E2 t1 t2 H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & EQ1 & pm1 & pm2 & D2 & EQ2 & SAT1 & SAT2).
  clarify. red in D1.
  specialize D1 with (expr_denot E1 s).
  simpls. desf; intuition desf.
Qed.

(** Points-to ownership predicates may be _split_. *)

Lemma assn_pointsto_split_std :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  assn_entails
    (Apointsto PTTstd (q1 + q2) E1 E2)
    (Astar (Apointsto PTTstd q1 E1 E2) (Apointsto PTTstd q2 E1 E2)).
Proof.
  intros q1 q2 E1 E2 H1 ph pm s g H2 H3 H4.
  unfold assn_sat in *.
  pose (v := expr_denot E2 s).
  assert (H5 : phc_add (PHCstd q1 v) (PHCstd q2 v) = PHCstd (q1 + q2) v). {
  unfold phc_add. desf. }
  assert (H6 : phc_disj (PHCstd q1 v) (PHCstd q2 v)). { red. intuition. }
  subst v. rewrite <- H5 in H4. clear H5.
  apply phc_le_diff in H4; vauto.
  (* satisfiability *)
  - destruct H4 as (phc & H4 & H5).
    pose (l := expr_denot E1 s).
    pose (v := expr_denot E2 s).
    exists (update ph l (PHCstd q1 v)).
    exists (update permheap_iden l (phc_add (PHCstd q2 v) phc)).
    repeat split; vauto.
    { (* disjointness *)
    intro l'. unfold update. desf; auto.
    by apply phc_disj_assoc_l. }
    { (* addition *)
    extensionality l'. unfold permheap_add, update.
    desf. by rewrite phc_add_assoc.
    unfold permheap_iden. by rewrite phc_add_iden_l. }
    exists procmap_iden, pm. repeat split; auto.
    by rewrite procmap_add_iden_r.
    { (* satisfiability - left *)
    unfold update. desf. }
    { (* satisfiability - right *)
    unfold update, permheap_iden. desf.
    apply phc_le_mono_pos.
    by apply phc_disj_add_l with (PHCstd q1 v). }
  (* validity *)
  - by apply phc_add_valid.
Qed.

Lemma assn_pointsto_split_proc :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  assn_entails
    (Apointsto PTTproc (q1 + q2) E1 E2)
    (Astar (Apointsto PTTproc q1 E1 E2) (Apointsto PTTproc q2 E1 E2)).
Proof.
  intros q1 q2 E1 E2 H1 ph pm s g H2 H3 H4.
  unfold assn_sat in *.
  pose (v := expr_denot E2 s).
  assert (H5 : phc_add (PHCproc q1 v) (PHCproc q2 v) = PHCproc (q1 + q2) v). {
  unfold phc_add. desf. }
  assert (H6 : phc_disj (PHCproc q1 v) (PHCproc q2 v)). { red. intuition. }
  subst v. rewrite <- H5 in H4. clear H5.
  apply phc_le_diff in H4; vauto.
  (* satisfiability *)
  - destruct H4 as (phc & H4 & H5).
    pose (l := expr_denot E1 s).
    pose (v := expr_denot E2 s).
    exists (update ph l (PHCproc q1 v)).
    exists (update permheap_iden l (phc_add (PHCproc q2 v) phc)).
    repeat split; vauto.
    { (* disjointness *)
    intro l'. unfold update. desf; auto.
    by apply phc_disj_assoc_l. }
    { (* addition *)
    extensionality l'. unfold permheap_add, update.
    desf. by rewrite phc_add_assoc.
    unfold permheap_iden. by rewrite phc_add_iden_l. }
    exists procmap_iden, pm. repeat split; auto.
    by rewrite procmap_add_iden_r.
    { (* satisfiability - left *)
    unfold update. desf. }
    { (* satisfiability - right *)
    unfold update, permheap_iden. desf.
    apply phc_le_mono_pos.
    by apply phc_disj_add_l with (PHCproc q1 v). }
  (* validity *)
  - by apply phc_add_valid.
Qed.

Lemma assn_pointsto_split_act :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  assn_entails
    (Apointsto PTTact (q1 + q2) E1 E2)
    (Astar (Apointsto PTTact q1 E1 E2) (Apointsto PTTact q2 E1 E2)).
Proof.
  intros q1 q2 E1 E2 H1 ph pm s g H2 H3 H4.
  unfold assn_sat in *.
  destruct H4 as (v' & H4).
  pose (v := expr_denot E2 s).
  assert (H5 : phc_add (PHCact q1 v v') (PHCact q2 v v') = PHCact (q1 + q2) v v'). {
  unfold phc_add. desf. }
  assert (H6 : phc_disj (PHCact q1 v v') (PHCact q2 v v')). { red. intuition. }
  subst v. rewrite <- H5 in H4. clear H5.
  apply phc_le_diff in H4; vauto.
  (* satisfiability *)
  - destruct H4 as (phc & H4 & H5).
    pose (l := expr_denot E1 s).
    pose (v := expr_denot E2 s).
    exists (update ph l (PHCact q1 v v')).
    exists (update permheap_iden l (phc_add (PHCact q2 v v') phc)).
    repeat split; vauto.
    { (* disjointness *)
    intro l'. unfold update. desf; auto.
    by apply phc_disj_assoc_l. }
    { (* addition *)
    extensionality l'. unfold permheap_add, update.
    desf. by rewrite phc_add_assoc.
    unfold permheap_iden. by rewrite phc_add_iden_l. }
    exists procmap_iden, pm. repeat split; auto.
    by rewrite procmap_add_iden_r.
    { (* satisfiability - left *)
    exists v'. unfold update. desf. }
    { (* satisfiability - right *)
    exists v'. unfold update, permheap_iden.
    desf. apply phc_le_mono_pos.
    by apply phc_disj_add_l with (PHCact q1 v v'). }
  (* validity *)
  - by apply phc_add_valid.
Qed.

Theorem assn_pointsto_split :
  forall q1 q2 E1 E2 t,
  perm_disj q1 q2 ->
  assn_entails
    (Apointsto t (q1 + q2) E1 E2)
    (Astar (Apointsto t q1 E1 E2) (Apointsto t q2 E1 E2)).
Proof.
  intros q1 q2 E1 E2 t H. destruct t.
  - by apply assn_pointsto_split_std.
  - by apply assn_pointsto_split_proc.
  - by apply assn_pointsto_split_act.
Qed.

(** Points-to ownership predicates may be _merged_. *)

Lemma assn_pointsto_merge_std :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  assn_entails
    (Astar (Apointsto PTTstd q1 E1 E2) (Apointsto PTTstd q2 E1 E2))
    (Apointsto PTTstd (q1 + q2) E1 E2).
Proof.
  unfold assn_entails.
  intros q1 q2 E1 E2 D1 ph pm s g V1 V2 SAT.
  unfold assn_sat in *.
  destruct SAT as (ph1 & ph2 & D2 & H1 & pm1 & pm2 & D3 & H2 & LE1 & LE2).
  clarify. rewrite <- permheap_add_cell.
  pose (v := expr_denot E2 s).
  assert (H6 : PHCstd (q1 + q2) v = phc_add (PHCstd q1 v) (PHCstd q2 v)). {
  unfold phc_add. desf. }
  subst v. rewrite H6.
  apply phc_le_compat; vauto.
  apply phc_le_diff in LE1; auto.
  - destruct LE1 as (phc & D4 & H3).
    apply phc_disj_add_l with phc; auto.
    rewrite phc_add_comm. by rewrite H3.
  - by apply perm_disj_valid_l in D1.
  - by apply permheap_disj_valid_l in D2.
Qed.

Lemma assn_pointsto_merge_proc :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  assn_entails
    (Astar (Apointsto PTTproc q1 E1 E2) (Apointsto PTTproc q2 E1 E2))
    (Apointsto PTTproc (q1 + q2) E1 E2).
Proof.
  unfold assn_entails.
  intros q1 q2 E1 E2 D1 ph pm s g V1 V2 SAT.
  unfold assn_sat in *.
  destruct SAT as (ph1 & ph2 & D2 & H1 & pm1 & pm2 & D3 & H2 & LE1 & LE2).
  clarify. rewrite <- permheap_add_cell.
  pose (v := expr_denot E2 s).
  assert (H6 : PHCproc (q1 + q2) v = phc_add (PHCproc q1 v) (PHCproc q2 v)). {
  unfold phc_add. desf. }
  subst v. rewrite H6.
  apply phc_le_compat; vauto.
  apply phc_le_diff in LE1; auto.
  - destruct LE1 as (phc & D4 & H3).
    apply phc_disj_add_l with phc; auto.
    rewrite phc_add_comm. by rewrite H3.
  - by apply perm_disj_valid_l in D1.
  - by apply permheap_disj_valid_l in D2.
Qed.

Lemma assn_pointsto_merge_act :
  forall q1 q2 E1 E2,
  perm_disj q1 q2 ->
  assn_entails
    (Astar (Apointsto PTTact q1 E1 E2) (Apointsto PTTact q2 E1 E2))
    (Apointsto PTTact (q1 + q2) E1 E2).
Proof.
  unfold assn_entails.
  intros q1 q2 E1 E2 D1 ph pm s g V1 V2 SAT.
  unfold assn_sat in *.
  destruct SAT as (ph1 & ph2 & D2 & H1 & pm1 & pm2 & D3 & H2 & LE1 & LE2).
  clarify. rewrite <- permheap_add_cell.
  destruct LE1 as (v1 & LE1).
  destruct LE2 as (v2 & LE2).
  assert (H3 : v1 = v2). {
  unfold permheap_disj, phc_disj in D2.
  specialize D2 with (expr_denot E1 s).
  unfold phc_le in LE1, LE2. repeat desf. }
  clarify. exists v2.
  pose (v := expr_denot E2 s).
  assert (H6 : PHCact (q1 + q2) v v2 = phc_add (PHCact q1 v v2) (PHCact q2 v v2)). {
  unfold phc_add. desf. }
  subst v. rewrite H6.
  apply phc_le_compat; vauto.
  apply phc_le_diff in LE1; auto.
  - destruct LE1 as (phc & D4 & H3).
    apply phc_disj_add_l with phc; auto.
    rewrite phc_add_comm. by rewrite H3.
  - by apply perm_disj_valid_l in D1.
  - by apply permheap_disj_valid_l in D2.
Qed.

Theorem assn_pointsto_merge :
  forall q1 q2 E1 E2 t,
  perm_disj q1 q2 ->
  assn_entails
    (Astar (Apointsto t q1 E1 E2) (Apointsto t q2 E1 E2))
    (Apointsto t (q1 + q2) E1 E2).
Proof.
  intros q1 q2 E1 E2 t H1. destruct t.
  - by apply assn_pointsto_merge_std.
  - by apply assn_pointsto_merge_proc.
  - by apply assn_pointsto_merge_act.
Qed.

(** Rules for 'process-action' ownership predicates, which allow to use
    such predicates as abbreviations for process- and action ownership predicates *)

Lemma assn_proc_procact_l :
  forall q E1 E2,
  q <> perm_full ->
  assn_entails (Apointsto_procact q E1 E2) (Apointsto PTTproc q E1 E2).
Proof.
  intros q E1 E2 H1 ph pm s g V1 V2 SAT.
  unfold Apointsto_procact in SAT. desf.
Qed.

Lemma assn_proc_procact_r :
  forall q E1 E2,
  q <> perm_full ->
  assn_entails (Apointsto PTTproc q E1 E2) (Apointsto_procact q E1 E2).
Proof.
  intros q E1 E2 H1 ph pm s g V1 V2 SAT.
  unfold Apointsto_procact. desf.
Qed.

Lemma assn_act_procact_l :
  forall E1 E2,
  assn_entails (Apointsto_procact perm_full E1 E2) (Apointsto PTTact perm_full E1 E2).
Proof.
  intros E1 E2 ph pm s g V1 V2 SAT.
  unfold Apointsto_procact in SAT. desf.
Qed.

Lemma assn_act_procact_r :
  forall E1 E2,
  assn_entails (Apointsto PTTact perm_full E1 E2) (Apointsto_procact perm_full E1 E2).
Proof.
  intros E1 E2 ph pm s g V1 V2 SAT.
  unfold Apointsto_procact. desf.
Qed.

Lemma assn_iter_proc_procact_l {T} :
  forall (xs : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x <> perm_full) ->
  assn_entails (Aiter (pointsto_iter_procact xs fq f1 f2)) (Aiter (pointsto_iter xs fq f1 f2 PTTproc)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f1 f2 fq H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2). vauto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  (* the head of the iterated conjunction is satisfied *)
  - apply assn_proc_procact_l; auto.
    + intro H2. apply H1 with x; vauto.
    + by apply permheap_disj_valid_l in D1.
    + by apply procmap_disj_valid_l in D2.
  (* the tail of the iterated conjunction is satisfied *)
  - apply IH; vauto.
    + intros y H2 H4. apply H1 with y; vauto.
    + by apply permheap_disj_valid_r in D1.
    + by apply procmap_disj_valid_r in D2.
Qed.

Lemma assn_iter_proc_procact_r {T} :
  forall (xs : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x <> perm_full) ->
  assn_entails (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) (Aiter (pointsto_iter_procact xs fq f1 f2)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f1 f2 fq H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2). vauto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  (* the head of the iterated conjunction is satisfied *)
  - apply assn_proc_procact_r; auto.
    + intro H2. apply H1 with x; vauto.
    + by apply permheap_disj_valid_l in D1.
    + by apply procmap_disj_valid_l in D2.
  (* the tail of the iterated conjunction is satisfied *)
  - apply IH; vauto.
    + intros y H2 H4. apply H1 with y; vauto.
    + by apply permheap_disj_valid_r in D1.
    + by apply procmap_disj_valid_r in D2.
Qed.

Lemma assn_iter_act_procact_l {T} :
  forall (xs : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x = perm_full) ->
  assn_entails (Aiter (pointsto_iter_procact xs fq f1 f2)) (Aiter (pointsto_iter xs fq f1 f2 PTTact)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f1 f2 fq H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2). vauto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  (* the head of the iterated conjunction is satisfied *)
  - rewrite H1; vauto. apply assn_act_procact_l; auto.
    + by apply permheap_disj_valid_l in D1.
    + by apply procmap_disj_valid_l in D2.
    + rewrite <- H1 with x; vauto.
  (* the tail of the iterated conjunction is satisfied *)
  - apply IH; vauto.
    + intros y H2. apply H1. vauto.
    + by apply permheap_disj_valid_r in D1.
    + by apply procmap_disj_valid_r in D2.
Qed.

Lemma assn_iter_act_procact_r {T} :
  forall (xs : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x = perm_full) ->
  assn_entails (Aiter (pointsto_iter xs fq f1 f2 PTTact)) (Aiter (pointsto_iter_procact xs fq f1 f2)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros f1 f2 fq H1 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2). vauto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  (* the head of the iterated conjunction is satisfied *)
  - rewrite H1; vauto. apply assn_act_procact_r; auto.
    + by apply permheap_disj_valid_l in D1.
    + by apply procmap_disj_valid_l in D2.
    + rewrite <- H1 with x; vauto.
  (* the tail of the iterated conjunction is satisfied *)
  - apply IH; vauto.
    + intros y H2. apply H1. vauto.
    + by apply permheap_disj_valid_r in D1.
    + by apply procmap_disj_valid_r in D2.
Qed.

Theorem pointsto_iter_procact_split {T} :
  forall (xs ys : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x <> perm_full) ->
    (forall x : T, In x ys -> fq x = perm_full) ->
  assn_entails
    (Aiter (pointsto_iter_procact (xs ++ ys) fq f1 f2))
    (Astar (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) (Aiter (pointsto_iter ys fq f1 f2 PTTact))).
Proof.
  intros xs ys f1 f2 q1 H1 H2 ph pm s g V1 V2 SAT.
  rewrite <- pointsto_iter_procact_app in SAT.
  apply assn_iter_add_r in SAT; auto.
  destruct SAT as (ph1 & ph2 & D1 & H3 & pm1 & pm2 & D2 & H4 & SAT1 & SAT2).
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  (* the process points-to predicates are satisfied *)
  - apply assn_iter_proc_procact_l; auto.
    + by apply permheap_disj_valid_l in D1.
    + by apply procmap_disj_valid_l in D2.
  (* the action points-to predicates are satisfied *)
  - apply assn_iter_act_procact_l; auto.
    + by apply permheap_disj_valid_r in D1.
    + by apply procmap_disj_valid_r in D2.
Qed.

Theorem pointsto_iter_procact_merge {T} :
  forall (xs ys : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
    (forall x : T, In x xs -> fq x <> perm_full) ->
    (forall x : T, In x ys -> fq x = perm_full) ->
  assn_entails
    (Astar (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) (Aiter (pointsto_iter ys fq f1 f2 PTTact)))
    (Aiter (pointsto_iter_procact (xs ++ ys) fq f1 f2)).
Proof.
  intros xs ys f1 f2 q1 H1 H2 ph pm s g V1 V2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H3 & pm1 & pm2 & D2 & H4 & SAT1 & SAT2).
  rewrite <- pointsto_iter_procact_app.
  apply assn_iter_add_l; auto.
  exists ph1, ph2. intuition vauto.
  exists pm1, pm2. intuition vauto.
  (* the process points-to predicates are satisfied *)
  - apply assn_iter_proc_procact_r; auto.
    + by apply permheap_disj_valid_l in D1.
    + by apply procmap_disj_valid_l in D2.
  (* the action points-to predicates are satisfied *)
  - apply assn_iter_act_procact_r; auto.
    + by apply permheap_disj_valid_r in D1.
    + by apply procmap_disj_valid_r in D2.
Qed.

Corollary pointsto_iter_procact_partition {T} :
  forall (xs ys1 ys2 : list T)(f1 f2 : T -> Expr)(fq : T -> Qc),
  let f := fun x : T => if Qc_eq_dec (fq x) perm_full then false else true in
  partition f xs = (ys1, ys2) ->
  assn_entails
    (Aiter (pointsto_iter_procact xs fq f1 f2))
    (Astar (Aiter (pointsto_iter ys1 fq f1 f2 PTTproc)) (Aiter (pointsto_iter ys2 fq f1 f2 PTTact))).
Proof.
  intros xs ys1 ys2 f1 f2 fq f H1 ph pm s g V1 V2 SAT.
  assert (H2 : Permutation xs (ys1 ++ ys2)). { by apply partition_permut with f. }
  apply assn_sat_procact_iter_permut with (ys := ys1 ++ ys2) in SAT; vauto.
  apply pointsto_iter_procact_split; vauto.
  (* all elements of [ys1] have read-only permission *)
  - intros x H3. apply partition_f_left with (x0 := x) in H1; auto.
    subst f. simpl in H1. desf.
  (* all elements of [ys2] have write permission *)
  - intros x H3. apply partition_f_right with (x0 := x) in H1; auto.
    subst f. simpl in H1. desf.
Qed.


(** *** Process ownership predicates *)

Theorem assn_proc :
  forall P1 P2 x q p xs f,
  proc_bisim P1 P2 ->
  assn_entails (Aproc x q p P1 xs f) (Aproc x q p P2 xs f).
Proof.
  intros P1 P2 x q p xs f H ph pm s g H2 H3 H4.
  unfold assn_sat in *.
  destruct H4 as (pmv & H4 & H5).
  exists pmv. intuition.
  transitivity (pmv_add (PMelem q p P1 xs (expr_denot_map f s)) pmv); auto.
  by rewrite <- H5, <- H.
Qed.

Theorem assn_proc_split :
  forall q1 q2 x p P1 P2 xs f,
  perm_disj q1 q2 ->
  assn_entails
    (Aproc x (q1 + q2) p (Ppar P1 P2) xs f)
    (Astar (Aproc x q1 p P1 xs f) (Aproc x q2 p P2 xs f)).
Proof.
  intros q1 q2 x p P1 P2 xs f H1 ph pm s g H2 H3 H4.
  unfold assn_sat in H4.
  destruct H4 as (pmv & H4 & H5).
  exists permheap_iden, ph. intuition.
  by apply permheap_add_iden_r.
  exists (update procmap_iden (g x) (PMelem q1 p P1 xs (expr_denot_map f s))).
  exists (update pm (g x) (pmv_add (PMelem q2 p P2 xs (expr_denot_map f s)) pmv)).
  intuition vauto.
  (* disjointness *)
  - apply procmap_disj_upd; auto.
    apply pmv_disj_assoc_l; auto.
    + unfold pmv_disj. intuition.
    + unfold pmv_add. desf.
  (* addition *)
  - intro pid.
    unfold procmap_add, update.
    destruct (Z.eq_dec (g x) pid); vauto.
    + rewrite H5. rewrite <- pmv_add_assoc.
      unfold pmv_add. desf.
    + by rewrite pmv_add_iden_r.
  (* satisfiability - left *)
  - exists PMfree. intuition clarify.
    + apply pmv_disj_iden_l.
      unfold pmv_valid.
      by apply perm_disj_valid_l in H1.
    + unfold update. desf.
  (* satisfiability - right *)
  - exists pmv. intuition clarify.
    apply pmv_disj_add_l with (PMelem q1 p P1 xs (expr_denot_map f s)).
    + unfold pmv_disj. intuition vauto.
    + unfold pmv_add. desf.
    + unfold update. desf.
Qed.

Theorem assn_proc_merge :
  forall q1 q2 x p P1 P2 xs f,
  perm_disj q1 q2 ->
  assn_entails
    (Astar (Aproc x q1 p P1 xs f) (Aproc x q2 p P2 xs f))
    (Aproc x (q1 + q2) p (Ppar P1 P2) xs f).
Proof.
  intros q1 q2 x p P1 P2 xs f H1 ph pm s g H2 H3 H4.
  unfold assn_sat in H4.
  destruct H4 as (ph1 & ph2 & D1 & H4 & pm1 & pm2 & D2 & H5 & SAT1 & SAT2).
  destruct SAT1 as (pmv1 & S1 & S2).
  destruct SAT2 as (pmv2 & S3 & S4).
  exists (pmv_add pmv1 pmv2). intuition clarify.
  (* disjointness *)
  - rewrite <- pmv_add_elem.
    apply pmv_disj_compat; vauto.
    rewrite <- S2, <- S4.
    by apply D2.
  (* proper addition *)
  - rewrite <- pmv_add_elem.
    rewrite pmv_add_compat.
    rewrite <- S2, <- S4.
    rewrite procmap_add_pmv.
    intuition.
Qed.

Theorem assn_proc_weaken :
  forall q1 q2 x p P1 P2 xs f,
  perm_disj q1 q2 ->
  assn_entails
    (Aproc x (q1 + q2) p (Ppar P1 P2) xs f)
    (Aproc x q1 p P1 xs f).
Proof.
  intros q1 q2 x p P1 P2 xs f H.
  transitivity (Astar (Aproc x q1 p P1 xs f) (Aproc x q2 p P2 xs f)).
  by apply assn_proc_split.
  apply assn_weaken.
Qed.


(** ** Iterated points-to predicates *)

Lemma assn_sat_pointsto_iter_indep {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr) ph pm1 pm2 s g t,
  procmap_valid pm2 ->
  assn_sat ph pm1 s g (Aiter (pointsto_iter xs fq f1 f2 t)) ->
  assn_sat ph pm2 s g (Aiter (pointsto_iter xs fq f1 f2 t)).
Proof.
  induction xs as [|l xs IH]. vauto.
  intros fq f1 f2 ph pm1 pm2 s g t V1 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1' & pm2' & D2 & H2 & SAT1 & SAT2).
  exists ph1, ph2. intuition vauto.
  exists procmap_iden, pm2. intuition vauto.
  (* the composition [iden + pm2] equals [pm2] (trivial) *)
  - by rewrite procmap_add_iden_r.
  (* postcondition is satisfied *)
  - apply IH with pm2'; auto.
Qed.

(** The satisfiability of iterated points-to predicates implies the satisfiability
    of a single points-to predicate. *)

Lemma pointsto_iter_sat_single_std {T} :
  forall (xs : list T)(x : T) ph pm s g F f1 f2,
  In x xs ->
  assn_sat ph pm s g (Aiter (pointsto_iter xs F f1 f2 PTTstd)) ->
  let q := F x in
  let l := expr_denot (f1 x) s in
  let v := expr_denot (f2 x) s in
  phc_le (PHCstd q v) (ph l).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros y ph pm s g F f1 f2 H1 SAT q l v.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
  simpl in H1. destruct H1 as [H1 | H1].
  (* [x] is at the head of [xs] *)
  - clarify. unfold assn_sat in SAT1.
    transitivity (ph1 l); vauto. rewrite <- permheap_add_cell.
    by apply phc_le_mono_pos.
  (* [x] is in the tail of [xs] *)
  - apply IH with (x := y) in SAT2; vauto.
    transitivity (ph2 l); vauto. rewrite <- permheap_add_cell.
    rewrite phc_add_comm. apply phc_le_mono_pos. by symmetry.
Qed.

Lemma pointsto_iter_sat_single_proc {T} :
  forall (xs : list T)(x : T) ph pm s g F f1 f2,
  In x xs ->
  assn_sat ph pm s g (Aiter (pointsto_iter xs F f1 f2 PTTproc)) ->
  let q := F x in
  let l := expr_denot (f1 x) s in
  let v := expr_denot (f2 x) s in
  phc_le (PHCproc q v) (ph l).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros y ph pm s g F f1 f2 H1 SAT q l v.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
  simpl in H1. destruct H1 as [H1 | H1].
  (* [x] is at the head of [xs] *)
  - clarify. unfold assn_sat in SAT1.
    transitivity (ph1 l); vauto. rewrite <- permheap_add_cell.
    by apply phc_le_mono_pos.
  (* [x] is in the tail of [xs] *)
  - apply IH with (x := y) in SAT2; vauto.
    transitivity (ph2 l); vauto. rewrite <- permheap_add_cell.
    rewrite phc_add_comm. apply phc_le_mono_pos. by symmetry.
Qed.

Lemma pointsto_iter_sat_single_act {T} :
  forall (xs : list T)(x : T) ph pm s g F f1 f2,
  In x xs ->
  assn_sat ph pm s g (Aiter (pointsto_iter xs F f1 f2 PTTact)) ->
  let q := F x in
  let l := expr_denot (f1 x) s in
  let v := expr_denot (f2 x) s in
  exists v', phc_le (PHCact q v v') (ph l).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros y ph pm s g F f1 f2 H1 SAT q l v.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
  simpl in H1. destruct H1 as [H1 | H1].
  (* [x] is at the head of [xs] *)
  - clarify. unfold assn_sat in SAT1.
    destruct SAT1 as (v' & SAT1). exists v'.
    transitivity (ph1 l); vauto. rewrite <- permheap_add_cell.
    by apply phc_le_mono_pos.
  (* [x] is in the tail of [xs] *)
  - apply IH with (x := y) in SAT2; vauto.
    destruct SAT2 as (v' & SAT2). exists v'.
    transitivity (ph2 l); vauto. rewrite <- permheap_add_cell.
    rewrite phc_add_comm. apply phc_le_mono_pos. by symmetry.
Qed.

(** Relations between the satisfiability of assertions and converted heap cells. *)

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_pointsto_conv_std :
  forall ph pm s g q E1 E2 l,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto PTTstd q E1 E2) ->
  assn_sat (permheap_conv_std ph l) pm s g (Apointsto PTTstd q E1 E2).
Proof.
  intros ph pm s g q E1 E2 l V1 SAT.
  unfold assn_sat, permheap_conv_std, update in *. desf.
  rewrite phc_std_conv. apply phc_conv_std_le; auto.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_pointsto_conv_proc :
  forall ph pm s g q E1 E2 l,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto PTTproc q E1 E2) ->
  assn_sat (permheap_conv_proc ph l) pm s g (Apointsto PTTproc q E1 E2).
Proof.
  intros ph pm s g q E1 E2 l V1 SAT.
  unfold assn_sat, permheap_conv_proc, update in *. desf.
  rewrite phc_proc_conv. apply phc_conv_proc_le; auto.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_pointsto_conv_act :
  forall ph pm s g q E1 E2 l,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto PTTact q E1 E2) ->
  assn_sat (permheap_conv_act ph l) pm s g (Apointsto PTTact q E1 E2).
Proof.
  intros ph pm s g q E1 E2 l V1 SAT.
  unfold assn_sat in *. destruct SAT as (v' & SAT).
  exists v'. unfold permheap_conv_act, update in *. desf.
  rewrite phc_act_conv. apply phc_conv_act_le; auto.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_pointsto_conv_std_mult :
  forall (ls : list Loc) ph pm s g q E1 E2,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto PTTstd q E1 E2) ->
  assn_sat (permheap_conv_std_mult ph ls) pm s g (Apointsto PTTstd q E1 E2).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros ph pm s g q E1 E2 V1 SAT.
  simpl (permheap_conv_std_mult ph (l :: ls)).
  apply assn_sat_pointsto_conv_std; auto.
  by apply permheap_conv_std_mult_valid.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_pointsto_conv_proc_mult :
  forall (ls : list Loc) ph pm s g q E1 E2,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto PTTproc q E1 E2) ->
  assn_sat (permheap_conv_proc_mult ph ls) pm s g (Apointsto PTTproc q E1 E2).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros ph pm s g q E1 E2 V1 SAT.
  simpl (permheap_conv_proc_mult ph (l :: ls)).
  apply assn_sat_pointsto_conv_proc; auto.
  by apply permheap_conv_proc_mult_valid.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_pointsto_conv_act_mult :
  forall (ls : list Loc) ph pm s g q E1 E2,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto PTTact q E1 E2) ->
  assn_sat (permheap_conv_act_mult ph ls) pm s g (Apointsto PTTact q E1 E2).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros ph pm s g q E1 E2 V1 SAT.
  simpl (permheap_conv_act_mult ph (l :: ls)).
  apply assn_sat_pointsto_conv_act; auto.
  by apply permheap_conv_act_mult_valid.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_iter_conv_std {T} :
  forall (xs : list T)(l : Loc) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  assn_sat ph pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTstd)) ->
  assn_sat (permheap_conv_std ph l) pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTstd)).
Proof.
  induction xs as [|x xs IH]. vauto. intros l ph pm s g f1 f2 fq SAT.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
  exists (permheap_conv_std ph1 l), (permheap_conv_std ph2 l).
  repeat split; vauto.
  (* the converted heaps [ph1] and [ph2] are disjoint *)
  - by apply permheap_conv_std_disj.
  (* the addition of the converted heaps [ph1] and [ph2] matches *)
  - by rewrite permheap_conv_std_add.
  (* the assertion holds *)
  - exists pm1, pm2. repeat split; vauto.
    (* the head of the iterated conjunction is satisfied *)
    + apply assn_sat_pointsto_conv_std; vauto.
      by apply permheap_disj_valid_l in D1.
    (* the tail of the iterated conjunction is satisfied *)
    + apply IH; vauto.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_iter_conv_proc {T} :
  forall (xs : list T)(l : Loc) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  assn_sat ph pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) ->
  assn_sat (permheap_conv_proc ph l) pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTproc)).
Proof.
  induction xs as [|x xs IH]. vauto. intros l ph pm s g f1 f2 fq SAT.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
  exists (permheap_conv_proc ph1 l), (permheap_conv_proc ph2 l).
  repeat split; vauto.
  (* the converted heaps [ph1] and [ph2] are disjoint *)
  - by apply permheap_conv_proc_disj.
  (* the addition of the converted heaps [ph1] and [ph2] matches *)
  - by rewrite permheap_conv_proc_add.
  (* the assertion holds *)
  - exists pm1, pm2. repeat split; vauto.
    (* the head of the iterated conjunction is satisfied *)
    + apply assn_sat_pointsto_conv_proc; vauto.
      by apply permheap_disj_valid_l in D1.
    (* the tail of the iterated conjunction is satisfied *)
    + apply IH; vauto.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_iter_conv_act {T} :
  forall (xs : list T)(l : Loc) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  assn_sat ph pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTact)) ->
  assn_sat (permheap_conv_act ph l) pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTact)).
Proof.
  induction xs as [|x xs IH]. vauto. intros l ph pm s g f1 f2 fq SAT.
  destruct SAT as (ph1 & ph2 & D1 & H2 & pm1 & pm2 & D2 & H3 & SAT1 & SAT2).
  exists (permheap_conv_act ph1 l), (permheap_conv_act ph2 l).
  repeat split; vauto.
  (* the converted heaps [ph1] and [ph2] are disjoint *)
  - by apply permheap_conv_act_disj.
  (* the addition of the converted heaps [ph1] and [ph2] matches *)
  - by rewrite permheap_conv_act_add.
  (* the assertion holds *)
  - exists pm1, pm2. repeat split; vauto.
    (* the head of the iterated conjunction is satisfied *)
    + apply assn_sat_pointsto_conv_act; vauto.
      by apply permheap_disj_valid_l in D1.
    (* the tail of the iterated conjunction is satisfied *)
    + apply IH; vauto.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_iter_conv_std_mult {T} :
  forall (ls : list Loc)(xs : list T) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  assn_sat ph pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTstd)) ->
  assn_sat (permheap_conv_std_mult ph ls) pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTstd)).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros xs ph pm s g f1 f2 fq SAT. simpl.
  by apply assn_sat_iter_conv_std, IH.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_iter_conv_proc_mult {T} :
  forall (ls : list Loc)(xs : list T) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  assn_sat ph pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) ->
  assn_sat (permheap_conv_proc_mult ph ls) pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTproc)).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros xs ph pm s g f1 f2 fq SAT. simpl.
  by apply assn_sat_iter_conv_proc, IH.
Qed.

(* note: the other direction of the rightmost implication does not hold *)
Lemma assn_sat_iter_conv_act_mult {T} :
  forall (ls : list Loc)(xs : list T) ph pm s g (f1 f2 : T -> Expr)(fq : T -> Qc),
  assn_sat ph pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTact)) ->
  assn_sat (permheap_conv_act_mult ph ls) pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTact)).
Proof.
  induction ls as [|l ls IH]. vauto.
  intros xs ph pm s g f1 f2 fq SAT. simpl.
  by apply assn_sat_iter_conv_act, IH.
Qed.

Lemma pointsto_conv_std :
  forall ph pm s g E1 E2 q t,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto t q E1 E2) ->
  let ph' := permheap_conv_std ph (expr_denot E1 s) in
  assn_sat ph' pm s g (Apointsto PTTstd q E1 E2).
Proof.
  intros ph pm s g E1 E2 q [ | | ] H1 SAT ph'.
  (* standard points-to predicate *)
  - unfold assn_sat in *. subst ph'.
    unfold permheap_conv_std, update. desf.
    replace (PHCstd q (expr_denot E2 s)) with (phc_conv_std (PHCstd q (expr_denot E2 s))); vauto.
    apply phc_conv_std_le; vauto.
  (* process points-to predicate *)
  - unfold assn_sat in *. subst ph'.
    unfold permheap_conv_std, update. desf.
    replace (PHCstd q (expr_denot E2 s)) with (phc_conv_std (PHCproc q (expr_denot E2 s))); vauto.
    apply phc_conv_std_le; vauto.
  (* action points-to predicate *)
  - unfold assn_sat in *. subst ph'.
    destruct SAT as (v' & SAT).
    unfold permheap_conv_std, update. desf.
    replace (PHCstd q (expr_denot E2 s)) with (phc_conv_std (PHCact q (expr_denot E2 s) v')); vauto.
    apply phc_conv_std_le; vauto.
Qed.

Lemma pointsto_conv_std_proc :
  forall ph pm s g E1 E2 q,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto PTTstd q E1 E2) ->
  let ph' := permheap_conv_proc ph (expr_denot E1 s) in
  assn_sat ph' pm s g (Apointsto PTTproc q E1 E2).
Proof.
  intros ph pm s g E1 E2 q H1 SAT ph'.
  unfold assn_sat in *. subst ph'.
  unfold permheap_conv_proc, update. desf.
  replace (PHCproc q (expr_denot E2 s)) with (phc_conv_proc (PHCstd q (expr_denot E2 s))); vauto.
  apply phc_conv_proc_le; vauto.
Qed.

Lemma pointsto_conv_proc_act :
  forall ph pm s g E1 E2 q,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto PTTproc q E1 E2) ->
  let ph' := permheap_conv_act ph (expr_denot E1 s) in
  assn_sat ph' pm s g (Apointsto PTTact q E1 E2).
Proof.
  intros ph pm s g E1 E2 q V1 SAT ph'.
  unfold assn_sat in *. subst ph'.
  unfold permheap_conv_act, update. desf.
  exists (expr_denot E2 s).
  replace (PHCact q (expr_denot E2 s) (expr_denot E2 s)) with (phc_conv_act (PHCproc q (expr_denot E2 s))); vauto.
  apply phc_conv_act_le; vauto.
Qed.

Lemma pointsto_conv_act_proc :
  forall ph pm s g E1 E2 q,
  permheap_valid ph ->
  assn_sat ph pm s g (Apointsto PTTact q E1 E2) ->
  let ph' := permheap_conv_proc ph (expr_denot E1 s) in
  assn_sat ph' pm s g (Apointsto PTTproc q E1 E2).
Proof.
  intros ph pm s g E1 E2 q V1 SAT ph'.
  unfold assn_sat in *. subst ph'.
  unfold permheap_conv_proc, update. desf.
  replace (PHCproc q (expr_denot E2 s)) with (phc_conv_proc (PHCact q (expr_denot E2 s) v')); vauto.
  apply phc_conv_proc_le; vauto.
Qed.

Lemma pointsto_iter_conv_std_proc {T} :
  forall (xs : list T) ph pm s g (f1 f2 : T -> Expr),
  let F := fun _ : T => perm_full in
  assn_sat ph pm s g (Aiter (pointsto_iter xs F f1 f2 PTTstd)) ->
  let xs' := map (expr_denot_map f1 s) xs in
  let ph' := permheap_conv_proc_mult ph xs' in
  assn_sat ph' pm s g (Aiter (pointsto_iter xs F f1 f2 PTTproc)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph pm s g f1 f2 F SAT xs' ph'.
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  assert (V3 : permheap_valid ph1). { by apply permheap_disj_valid_l in D1. }
  apply pointsto_conv_std_proc in SAT1; auto.
  apply IH in SAT2; clear IH.
  exists (permheap_conv_proc_mult ph1 (map (expr_denot_map f1 s) (x :: xs))).
  exists (permheap_conv_proc_mult ph2 (map (expr_denot_map f1 s) (x :: xs))).
  repeat split; vauto.
  (* after conversion, [ph1] is still disjoint with [ph2] *)
  - by apply permheap_conv_proc_mult_disj.
  (* the addition of the converted heaps equals [ph'] *)
  - rewrite <- permheap_conv_proc_mult_add; vauto.
  (* the assertion holds *)
  - exists pm1, pm2. intuition.
    (* the left part of the assertion holds *)
    + rewrite map_cons.
      rewrite permheap_conv_proc_mult_app with (xs := [expr_denot_map f1 s x])(ys := map (expr_denot_map f1 s) xs).
      rewrite permheap_conv_proc_mult_free with (xs := map (expr_denot_map f1 s) xs); [by vauto|].
      intros l H1. apply pointsto_iter_perm_full with (l0 := l) in SAT2; auto.
      rewrite permheap_conv_proc_mult_full in SAT2.
      unfold permheap_disj in D1. specialize D1 with l.
      symmetry in D1. by apply phc_disj_full_free in D1.
    (* the right part of the assertion holds *)
    + rewrite map_cons.
      rewrite permheap_conv_proc_mult_app with (xs := [expr_denot_map f1 s x])(ys := map (expr_denot_map f1 s) xs).
      rewrite permheap_conv_proc_mult_free with (xs := [expr_denot_map f1 s x]); [by vauto|].
      intros l H1. simpl in H1.
      destruct H1 as [H1 | H1]; vauto.
      subst F. simpl ((fun _ => perm_full) x) in SAT1.
      apply assn_pointsto_full in SAT1.
      * rewrite permheap_conv_proc_mult_free2.
        rewrite permheap_conv_proc_full in SAT1.
        replace (expr_denot_map f1 s x) with (expr_denot (f1 x) s); vauto.
        unfold permheap_disj in D1.
        specialize D1 with (expr_denot (f1 x) s).
        by apply phc_disj_full_free in D1.
      * apply permheap_conv_proc_valid.
        by apply permheap_disj_valid_l in D1.
Qed.

Lemma pointsto_iter_conv_proc_std {T} :
  forall (xs : list T) ph pm s g (f1 f2 : T -> Expr),
  let F := fun _ : T => perm_full in
  assn_sat ph pm s g (Aiter (pointsto_iter xs F f1 f2 PTTproc)) ->
  let xs' := map (expr_denot_map f1 s) xs in
  let ph' := permheap_conv_std_mult ph xs' in
  assn_sat ph' pm s g (Aiter (pointsto_iter xs F f1 f2 PTTstd)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph pm s g f1 f2 F SAT xs' ph'.
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  assert (V2 : permheap_valid ph1). { by apply permheap_disj_valid_l in D1. }
  apply pointsto_conv_std in SAT1; auto.
  apply IH in SAT2; clear IH.
  (* the assertion is satisfied *)
  exists (permheap_conv_std_mult ph1 (map (expr_denot_map f1 s) (x :: xs))).
  exists (permheap_conv_std_mult ph2 (map (expr_denot_map f1 s) (x :: xs))).
  repeat split; vauto.
  (* after conversion, [ph1] is still disjoint with [ph2] *)
  - by apply permheap_conv_std_mult_disj.
  (* the addition of the converted heaps equals [ph'] *)
  - rewrite <- permheap_conv_std_mult_add; vauto.
    (* the assertion holds *)
  - exists pm1, pm2. intuition.
    (* the left part of the assertion holds *)
    + rewrite map_cons.
      rewrite permheap_conv_std_mult_app with (xs := [expr_denot_map f1 s x])(ys := map (expr_denot_map f1 s) xs).
      rewrite permheap_conv_std_mult_free with (xs := map (expr_denot_map f1 s) xs); [by vauto|].
      intros l H1. apply pointsto_iter_perm_full with (l0 := l) in SAT2; auto.
      rewrite permheap_conv_std_mult_full in SAT2.
      unfold permheap_disj in D1. specialize D1 with l.
      symmetry in D1. by apply phc_disj_full_free in D1.
    (* the right part of the assertion holds *)
    + rewrite map_cons.
      rewrite permheap_conv_std_mult_app with (xs := [expr_denot_map f1 s x])(ys := map (expr_denot_map f1 s) xs).
      rewrite permheap_conv_std_mult_free with (xs := [expr_denot_map f1 s x]); [by vauto|].
      intros l H1. simpl in H1.
      destruct H1 as [H1 | H1]; vauto.
      subst F. simpl ((fun _ => perm_full) x) in SAT1.
      apply assn_pointsto_full in SAT1.
      * rewrite permheap_conv_std_mult_free2.
        rewrite permheap_conv_std_full in SAT1.
        replace (expr_denot_map f1 s x) with (expr_denot (f1 x) s); vauto.
        unfold permheap_disj in D1.
        specialize D1 with (expr_denot (f1 x) s).
        by apply phc_disj_full_free in D1.
      * apply permheap_conv_std_valid.
        by apply permheap_disj_valid_l in D1.
Qed.

Lemma pointsto_iter_conv_proc_act {T} :
  forall (xs : list T) ph pm s g (f1 f2 : T -> Expr)(F : T -> Qc),
  assn_sat ph pm s g (Aiter (pointsto_iter xs F f1 f2 PTTproc)) ->
  let xs' := map (expr_denot_map f1 s) xs : list Loc in
  let ph' := permheap_conv_act_mult ph xs' in
  assn_sat ph' pm s g (Aiter (pointsto_iter xs F f1 f2 PTTact)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph pm s g f1 f2 F SAT1 xs' ph'.
  destruct SAT1 as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  assert (V1 : permheap_valid ph1). { by apply permheap_disj_valid_l in D1. }
  apply pointsto_conv_proc_act in SAT1; auto. apply IH in SAT2; clear IH.
  exists (permheap_conv_act_mult ph1 (map (expr_denot_map f1 s) (x :: xs))).
  exists (permheap_conv_act_mult ph2 (map (expr_denot_map f1 s) (x :: xs))).
  repeat split; vauto.
  (* after conversion, [ph1] is still disjoint with [ph2] *)
  - by apply permheap_conv_act_mult_disj.
  (* the addition of the converted heaps equals [ph'] *)
  - rewrite <- permheap_conv_act_mult_add; vauto.
  (* the assertion holds *)
  - exists pm1, pm2. intuition.
    (* the left part of the assertion holds *)
    + unfold assn_sat in SAT1. desf.
      unfold assn_sat. exists v'. rewrite map_cons.
      unfold expr_denot_map at 1.
      rewrite permheap_conv_act_mult_apply; vauto.
      by rewrite permheap_conv_act_apply in SAT1.
    (* the right part of the assertion holds *)
    + replace (x :: xs) with ([x] ++ xs); auto.
      rewrite map_app, permheap_conv_act_mult_app.
      by apply assn_sat_iter_conv_act_mult.
Qed.

Lemma pointsto_iter_conv_act_proc {T} :
  forall (xs : list T) ph pm s g (f1 f2 : T -> Expr)(F : T -> Qc),
  assn_sat ph pm s g (Aiter (pointsto_iter xs F f1 f2 PTTact)) ->
  let xs' := map (expr_denot_map f1 s) xs : list Loc in
  let ph' := permheap_conv_proc_mult ph xs' in
  assn_sat ph' pm s g (Aiter (pointsto_iter xs F f1 f2 PTTproc)).
Proof.
  induction xs as [|x xs IH]. vauto.
  intros ph pm s g f1 f2 F SAT1 xs' ph'.
  destruct SAT1 as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  assert (V1 : permheap_valid ph1). { by apply permheap_disj_valid_l in D1. }
  apply pointsto_conv_act_proc in SAT1; auto. apply IH in SAT2; clear IH.
  exists (permheap_conv_proc_mult ph1 (map (expr_denot_map f1 s) (x :: xs))).
  exists (permheap_conv_proc_mult ph2 (map (expr_denot_map f1 s) (x :: xs))).
  repeat split; vauto.
  (* after conversion, [ph1] is still disjoint with [ph2] *)
  - by apply permheap_conv_proc_mult_disj.
  (* the addition of the converted heaps equals [ph'] *)
  - rewrite <- permheap_conv_proc_mult_add; vauto.
  (* the assertion holds *)
  - exists pm1, pm2. intuition.
    (* the left part of the assertion holds *)
    + unfold assn_sat in SAT1. desf.
      unfold assn_sat. rewrite map_cons.
      unfold expr_denot_map at 1.
      rewrite permheap_conv_proc_mult_apply; vauto.
      by rewrite permheap_conv_proc_apply in SAT1.
    (* the right part of the assertion holds *)
    + replace (x :: xs) with ([x] ++ xs); auto.
      rewrite map_app, permheap_conv_proc_mult_app.
      by apply assn_sat_iter_conv_proc_mult.
Qed.

(** Relations between assertion satisfiability and heap disjointness, in combination
    with heap conversions. *)

Lemma assn_disj_sat_conv_std :
  forall ph1 ph2 pm s g E1 E2 q,
  permheap_valid ph1 ->
  assn_sat ph1 pm s g (Apointsto PTTstd q E1 E2) ->
  permheap_disj (permheap_conv_std ph1 (expr_denot E1 s)) ph2 <->
  permheap_disj ph1 ph2.
Proof.
  intros ph1 ph2 pm s g E1 E2 q V1 SAT. split; intro D1.
  (* left to right *)
  - unfold assn_sat in SAT.
    intro l. unfold permheap_conv_std in D1.
    unfold permheap_disj in D1. specialize D1 with l.
    unfold update in D1. desf.
    rewrite <- phc_le_conv_std_disj with q (expr_denot E2 s); auto.
  (* right to left *)
  - unfold assn_sat in SAT.
    intro l. unfold permheap_conv_std, update. desf.
    rewrite phc_le_conv_std_disj with q (expr_denot E2 s); auto.
Qed.

Lemma assn_disj_sat_conv_proc :
  forall ph1 ph2 pm s g E1 E2 q,
  permheap_valid ph1 ->
  assn_sat ph1 pm s g (Apointsto PTTproc q E1 E2) ->
  permheap_disj (permheap_conv_proc ph1 (expr_denot E1 s)) ph2 <->
  permheap_disj ph1 ph2.
Proof.
  intros ph1 ph2 pm s g E1 E2 q V1 SAT. split; intro D1.
  (* left to right *)
  - unfold assn_sat in SAT.
    intro l. unfold permheap_conv_proc in D1.
    unfold permheap_disj in D1. specialize D1 with l.
    unfold update in D1. desf.
    rewrite <- phc_le_conv_proc_disj with q (expr_denot E2 s); auto.
  (* right to left *)
  - unfold assn_sat in SAT.
    intro l. unfold permheap_conv_proc, update. desf.
    rewrite phc_le_conv_proc_disj with q (expr_denot E2 s); auto.
Qed.

Lemma assn_disj_sat_conv_act :
  forall ph1 ph2 pm s g E1 E2 q,
  permheap_valid ph1 ->
  assn_sat ph1 pm s g (Apointsto PTTact q E1 E2) ->
  permheap_disj (permheap_conv_act ph1 (expr_denot E1 s)) ph2 <->
  permheap_disj ph1 ph2.
Proof.
  intros ph1 ph2 pm s g E1 E2 q V1 SAT. split; intro D1.
  (* left to right *)
  - unfold assn_sat in SAT. destruct SAT as (v' & H1).
    intro l. unfold permheap_conv_act in D1.
    unfold permheap_disj in D1. specialize D1 with l.
    unfold update in D1. desf.
    rewrite <- phc_le_conv_act_disj with q (expr_denot E2 s) v'; auto.
  (* right to left *)
  - unfold assn_sat in SAT. destruct SAT as (v' & H1).
    intro l. unfold permheap_conv_act, update. desf.
    rewrite phc_le_conv_act_disj with q (expr_denot E2 s) v'; auto.
Qed.

Lemma assn_disj_sat_conv_std_In {T} :
  forall (xs : list T)(l : Loc)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  assn_sat ph1 pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTstd)) ->
  let ls := map (expr_denot_map f1 s) xs : list Loc in
  In l ls ->
  permheap_disj (permheap_conv_std ph1 l) ph2 <->
  permheap_disj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros l fq f1 f2 ph1 ph2 pm s g SAT ls H1.
  destruct SAT as (ph3 & ph4 & D2 & H2 & pm1 & pm2 & D3 & H3 & SAT1 & SAT2).
  split; intro D1.
  (* left to right *)
  - subst ls. simpl in H1. destruct H1 as [H1 | H1]; vauto.
    + unfold expr_denot_map in D1.
      rewrite assn_disj_sat_conv_std with (pm := pm)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x) in D1; auto.
      rewrite <- H3. by apply assn_sat_weaken.
    + rewrite IH with fq f1 f2 pm s g in D1; auto.
      rewrite <- H3. rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
  (* right to left *)
  - subst ls. simpl in H1. destruct H1 as [H1 | H1]; vauto.
    + unfold expr_denot_map.
      rewrite assn_disj_sat_conv_std with (pm := pm)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x); auto.
      clarify. rewrite <- H3. apply assn_sat_weaken; auto.
    + apply IH with fq f1 f2 pm s g; auto.
      rewrite <- H3. rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
Qed.

Lemma assn_disj_sat_conv_proc_In {T} :
  forall (xs : list T)(l : Loc)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  assn_sat ph1 pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) ->
  let ls := map (expr_denot_map f1 s) xs : list Loc in
  In l ls ->
  permheap_disj (permheap_conv_proc ph1 l) ph2 <->
  permheap_disj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros l fq f1 f2 ph1 ph2 pm s g SAT ls H1.
  destruct SAT as (ph3 & ph4 & D2 & H2 & pm1 & pm2 & D3 & H3 & SAT1 & SAT2).
  split; intro D1.
  (* left to right *)
  - subst ls. simpl in H1. destruct H1 as [H1 | H1]; vauto.
    + unfold expr_denot_map in D1.
      rewrite assn_disj_sat_conv_proc with (pm := pm)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x) in D1; auto.
      rewrite <- H3. by apply assn_sat_weaken.
    + rewrite IH with fq f1 f2 pm s g in D1; auto.
      rewrite <- H3. rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
  (* right to left *)
  - subst ls. simpl in H1. destruct H1 as [H1 | H1]; vauto.
    + unfold expr_denot_map.
      rewrite assn_disj_sat_conv_proc with (pm := pm)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x); auto.
      clarify. rewrite <- H3. apply assn_sat_weaken; auto.
    + apply IH with fq f1 f2 pm s g; auto.
      rewrite <- H3. rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
Qed.

Lemma assn_disj_sat_conv_act_In {T} :
  forall (xs : list T)(l : Loc)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  assn_sat ph1 pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTact)) ->
  let ls := map (expr_denot_map f1 s) xs : list Loc in
  In l ls ->
  permheap_disj (permheap_conv_act ph1 l) ph2 <->
  permheap_disj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros l fq f1 f2 ph1 ph2 pm s g SAT ls H1.
  destruct SAT as (ph3 & ph4 & D2 & H2 & pm1 & pm2 & D3 & H3 & SAT1 & SAT2).
  split; intro D1.
  (* left to right *)
  - subst ls. simpl in H1. destruct H1 as [H1 | H1]; vauto.
    + unfold expr_denot_map in D1.
      rewrite assn_disj_sat_conv_act with (pm := pm)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x) in D1; auto.
      rewrite <- H3. by apply assn_sat_weaken.
    + rewrite IH with fq f1 f2 pm s g in D1; auto.
      rewrite <- H3. rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
  (* right to left *)
  - subst ls. simpl in H1. destruct H1 as [H1 | H1]; vauto.
    + unfold expr_denot_map.
      rewrite assn_disj_sat_conv_act with (pm := pm)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x); auto.
      clarify. rewrite <- H3. apply assn_sat_weaken; auto.
    + apply IH with fq f1 f2 pm s g; auto.
      rewrite <- H3. rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
Qed.

Lemma assn_disj_sat_conv_std_mult {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  assn_sat ph1 pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTstd)) ->
  let ls := map (expr_denot_map f1 s) xs : list Loc in
  permheap_disj (permheap_conv_std_mult ph1 ls) ph2 <->
  permheap_disj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros fq f1 f2 ph1 ph2 pm s g SAT ls.
  destruct SAT as (ph3 & ph4 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  clarify. split; intro D3.
  (* left to right *)
  - subst ls. simpl in D3.
    rewrite <- IH with (pm := pm)(s := s)(g := g)(fq := fq)(f1 := f1)(f2 := f2).
    + rewrite <- assn_disj_sat_conv_std with (pm := pm)(s := s)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x); auto.
      * by apply permheap_conv_std_mult_valid, permheap_add_valid.
      * apply assn_sat_pointsto_conv_std_mult; auto.
        rewrite <- H2. by apply assn_sat_weaken.
    + rewrite <- H2. rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
  (* right or left *)
  - subst ls. simpl. unfold expr_denot_map at 2.
    rewrite assn_disj_sat_conv_std with (pm := pm)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x); auto.
    + apply IH with fq f2 pm g; auto. rewrite <- H2.
      rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
    + apply permheap_conv_std_mult_valid.
      by apply permheap_add_valid.
    + apply assn_sat_pointsto_conv_std_mult; auto.
      rewrite <- H2. by apply assn_sat_weaken.
Qed.

Lemma assn_disj_sat_conv_proc_mult {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  assn_sat ph1 pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) ->
  let ls := map (expr_denot_map f1 s) xs : list Loc in
  permheap_disj (permheap_conv_proc_mult ph1 ls) ph2 <->
  permheap_disj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros fq f1 f2 ph1 ph2 pm s g SAT ls.
  destruct SAT as (ph3 & ph4 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  clarify. split; intro D3.
  (* left to right *)
  - subst ls. simpl in D3.
    rewrite <- IH with (pm := pm)(s := s)(g := g)(fq := fq)(f1 := f1)(f2 := f2).
    + rewrite <- assn_disj_sat_conv_proc with (pm := pm)(s := s)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x); auto.
      * by apply permheap_conv_proc_mult_valid, permheap_add_valid.
      * apply assn_sat_pointsto_conv_proc_mult; auto.
        rewrite <- H2. by apply assn_sat_weaken.
    + rewrite <- H2. rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
  (* right or left *)
  - subst ls. simpl. unfold expr_denot_map at 2.
    rewrite assn_disj_sat_conv_proc with (pm := pm)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x); auto.
    + apply IH with fq f2 pm g; auto. rewrite <- H2.
      rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
    + apply permheap_conv_proc_mult_valid.
      by apply permheap_add_valid.
    + apply assn_sat_pointsto_conv_proc_mult; auto.
      rewrite <- H2. by apply assn_sat_weaken.
Qed.

Lemma assn_disj_sat_conv_act_mult {T} :
  forall (xs : list T)(fq : T -> Qc)(f1 f2 : T -> Expr) ph1 ph2 pm s g,
  assn_sat ph1 pm s g (Aiter (pointsto_iter xs fq f1 f2 PTTact)) ->
  let ls := map (expr_denot_map f1 s) xs : list Loc in
  permheap_disj (permheap_conv_act_mult ph1 ls) ph2 <->
  permheap_disj ph1 ph2.
Proof.
  induction xs as [|x xs IH]. vauto.
  intros fq f1 f2 ph1 ph2 pm s g SAT ls.
  destruct SAT as (ph3 & ph4 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  clarify. split; intro D3.
  (* left to right *)
  - subst ls. simpl in D3.
    rewrite <- IH with (pm := pm)(s := s)(g := g)(fq := fq)(f1 := f1)(f2 := f2).
    + rewrite <- assn_disj_sat_conv_act with (pm := pm)(s := s)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x); auto.
      * by apply permheap_conv_act_mult_valid, permheap_add_valid.
      * apply assn_sat_pointsto_conv_act_mult; auto.
        rewrite <- H2. by apply assn_sat_weaken.
    + rewrite <- H2. rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
  (* right or left *)
  - subst ls. simpl. unfold expr_denot_map at 2.
    rewrite assn_disj_sat_conv_act with (pm := pm)(g := g)(q := fq x)(E1 := f1 x)(E2 := f2 x); auto.
    + apply IH with fq f2 pm g; auto. rewrite <- H2.
      rewrite permheap_add_comm, procmap_add_comm.
      apply assn_sat_weaken; auto.
    + apply permheap_conv_act_mult_valid.
      by apply permheap_add_valid.
    + apply assn_sat_pointsto_conv_act_mult; auto.
      rewrite <- H2. by apply assn_sat_weaken.
Qed.
