Require Import Bool.
Require Import HahnBase.
Require Import List.
Require Import Prerequisites.
Require Import Setoid.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.

Open Scope Z_scope.


(** * Process Algebra Theory *)

(** This document contains the static and dynamics of process algebra terms, 
    as well as a soundness argument for an axiomatisation. *)

(** ** Statics *)

(** This section discusses the syntax of process-algebraic (Boolean) expressions
    and process algebra terms. *)

Definition ProcID := Z.
Definition ProcVar := Z.
Definition ProcVal := Z.
Definition ActLabel := Z.
Definition ProcLabel := Z.

Inductive ProcExpr :=
  | PEconst(n:ProcVal)
  | PEvar(x:ProcVar)
  | PEplus(e1 e2:ProcExpr).

Add Search Blacklist "ProcExpr_rect".
Add Search Blacklist "ProcExpr_ind".
Add Search Blacklist "ProcExpr_rec".

Inductive ProcBoolExpr :=
  | PBconst(b:bool)
  | PBnot(b:ProcBoolExpr)
  | PBand(b1 b2:ProcBoolExpr)
  | PBeq(e1 e2:ProcExpr).

Add Search Blacklist "ProcBoolExpr_rect".
Add Search Blacklist "ProcBoolExpr_ind".
Add Search Blacklist "ProcBoolExpr_rec".

Inductive Proc :=
  | Pdelta
  | Pepsilon
  | Pact(a:ActLabel)
  | Pseq(P1 P2:Proc)
  | Palt(P1 P2:Proc)
  | Ppar(P1 P2:Proc)
  | Plmerge(P1 P2:Proc)
  | Piter(P:Proc).

Add Search Blacklist "Proc_rect".
Add Search Blacklist "Proc_ind".
Add Search Blacklist "Proc_rec".

Lemma proc_par_neq_l :
  forall P Q, Ppar P Q <> Q.
Proof.
  induction Q; simpls.
  intuition congruence.
Qed.

Lemma proc_par_neq_r :
  forall P Q, Ppar Q P <> Q.
Proof.
  induction Q; simpls.
  intuition congruence.
Qed.

Lemma pexpr_eq_dec :
  forall e1 e2 : ProcExpr, { e1 = e2 } + { e1 <> e2 }.
Proof.
  decide equality; apply Z.eq_dec.
Qed.

Lemma pbexpr_eq_dec :
  forall b1 b2 : ProcBoolExpr, { b1 = b2 } + { b1 <> b2 }.
Proof.
  decide equality.
  apply Bool.bool_dec.
  apply pexpr_eq_dec.
  apply pexpr_eq_dec.
Qed.

Lemma proc_eq_dec :
  forall P1 P2 : Proc, { P1 = P2 } + { P1 <> P2 }.
Proof.
  decide equality.
  apply Z.eq_dec.
Qed.


(** *** Environments *)

(** The soundness argument of the program logic is parameterised by
    the following functions, which together constitute the environment
    in which process terms are used. *)

Parameter guard : ActLabel -> ProcBoolExpr.
Parameter effect : ActLabel -> ProcBoolExpr.
Parameter body : ProcLabel -> Proc.


(** *** Free variables *)

(** Free variables of process-algebraic expressions is defined in the standard way.
    The free variables [act_fv a] of an action [a] is determined by the free variables
    in the contract (guard and effect) of [a]. *)

Fixpoint pexpr_fv (e : ProcExpr) : list ProcVar :=
   match e with
    | PEconst _ => nil
    | PEvar x => [x]
    | PEplus e1 e2 => pexpr_fv e1 ++ pexpr_fv e2
  end.

Fixpoint pexpr_fv_list (xs : list ProcExpr) : list ProcVar :=
  match xs with
    | nil => nil
    | e :: xs' => pexpr_fv e ++ pexpr_fv_list xs'
  end.

Fixpoint pbexpr_fv (b : ProcBoolExpr) : list ProcVar :=
   match b with
    | PBconst _ => nil
    | PBnot b' => pbexpr_fv b'
    | PBand b1 b2 => pbexpr_fv b1 ++ pbexpr_fv b2
    | PBeq e1 e2 => pexpr_fv e1 ++ pexpr_fv e2
  end.

Definition act_fv (a : ActLabel) : list ProcVar :=
  pbexpr_fv (guard a) ++ pbexpr_fv (effect a).

Fixpoint proc_fv (P : Proc) : list ProcVar :=
  match P with
    | Pdelta
    | Pepsilon => nil
    | Pact a => act_fv a
    | Pseq P1 P2
    | Palt P1 P2
    | Ppar P1 P2
    | Plmerge P1 P2 => proc_fv P1 ++ proc_fv P2
    | Piter P' => proc_fv P'
  end.


(** ** Dynamics *)

(** This section contains the denotational- and operational semantics of process algebras. *)

Definition ProcStore := ProcVar -> ProcVal.


(** *** Denotational semantics *)

(** The denotational semantics of process-algebraic expressions is defined in the
    standard way. *)

Fixpoint pexpr_denot (e : ProcExpr)(ps : ProcStore) : ProcVal :=
  match e with
    | PEconst v => v
    | PEvar x => ps x
    | PEplus e1 e2 => pexpr_denot e1 ps + pexpr_denot e2 ps
  end.

Fixpoint pexpr_denot_list (xs : list ProcExpr)(ps : ProcStore) : list ProcVal :=
  match xs with
    | nil => nil
    | e :: xs' => pexpr_denot e ps :: pexpr_denot_list xs' ps
  end.

Fixpoint pbexpr_denot (b : ProcBoolExpr)(ps : ProcStore) : bool :=
  match b with
    | PBconst b => b
    | PBnot b' => negb (pbexpr_denot b' ps)
    | PBand b1 b2 => pbexpr_denot b1 ps && pbexpr_denot b2 ps
    | PBeq e1 e2 => if Z.eq_dec (pexpr_denot e1 ps) (pexpr_denot e2 ps) then true else false
  end.


(** *** Store agreement *)

(** Two process stores _agreeing_ on a set of process variables. *)

Definition pstore_agree (xs : list ProcVar)(ps1 ps2 : ProcStore) : Prop :=
  forall x : ProcVar, In x xs -> ps1 x = ps2 x.

Instance pstore_agree_symm (xs : list ProcVar) :
  Symmetric (pstore_agree xs).
Proof.
  intros ps1 ps2 H1 x H2. symmetry. by apply H1.
Qed.

Lemma pstore_agree_split :
  forall xs1 xs2 ps1 ps2,
  pstore_agree (xs1 ++ xs2) ps1 ps2 ->
  pstore_agree xs1 ps1 ps2 /\ pstore_agree xs2 ps1 ps2.
Proof.
  intros xs1 xs2 ps1 ps2 H1.
  split; intros x H2.
  - apply H1. apply in_or_app. by left.
  - apply H1. apply in_or_app. by right.
Qed.

Lemma pstore_agree_weaken :
  forall (xs1 xs2 : list ProcVar)(ps1 ps2 : ProcStore),
    (forall x : ProcVar, In x xs1 -> In x xs2) ->
  pstore_agree xs2 ps1 ps2 ->
  pstore_agree xs1 ps1 ps2.
Proof.
  intros xs1 xs2 ps1 ps2 H1 H2 ps H3.
  by apply H2, H1.
Qed.

(** The evaluation of process-algebraic (Boolean) expressions only depends
    on the free variables in the expressions. *)

Lemma pexpr_agree :
  forall e ps1 ps2,
  pstore_agree (pexpr_fv e) ps1 ps2 ->
  pexpr_denot e ps1 = pexpr_denot e ps2.
Proof.
  induction e; intros ps1 ps2 H; simpls.
  - apply H. vauto.
  - apply pstore_agree_split in H. des.
    by rewrite IHe1 with ps1 ps2, IHe2 with ps1 ps2.
Qed.

Lemma pbexpr_agree :
  forall b ps1 ps2,
  pstore_agree (pbexpr_fv b) ps1 ps2 ->
  pbexpr_denot b ps1 = pbexpr_denot b ps2.
Proof.
  induction b; intros ps1 ps2 H; simpls.
  - by rewrite IHb with ps1 ps2.
  - apply pstore_agree_split in H.
    destruct H as (H1 & H2).
    by rewrite IHb1 with ps1 ps2, IHb2 with ps1 ps2.
  - apply pstore_agree_split in H.
    destruct H as (H1 & H2).
    by rewrite pexpr_agree with e1 ps1 ps2, pexpr_agree with e2 ps1 ps2.
Qed.

(** Standard properties relating (Boolean) expression evaluation to store updates. *)

Lemma pexpr_denot_upd :
  forall e ps x v,
  ~ In x (pexpr_fv e) ->
  pexpr_denot e (update ps x v) = pexpr_denot e ps.
Proof.
  intros e ps x v H1.
  rewrite pexpr_agree with e ps (update ps x v); vauto.
  intros y H2. unfold update. desf.
Qed.

Lemma pbexpr_denot_upd :
  forall b ps x v,
  ~ In x (pbexpr_fv b) ->
  pbexpr_denot b (update ps x v) = pbexpr_denot b ps.
Proof.
  intros b ps x v H1.
  rewrite pbexpr_agree with b ps (update ps x v); vauto.
  intros y H2. unfold update. desf.
Qed.


(** *** Successful termination *)

(** We explicitly define a notion of termination via the predicate [proc_term P],
    which asserts that the process [P] has the choice to successfully terminate.
    Notably, [Pepsilon] always successfully terminates; [Pdelta] never successfully
    terminates; and [Piter P] may successfully terminate since there is a choice to
    iterate [P] zero times. *)

Inductive proc_term : Proc -> Prop :=
  (* epsilon *)
  | pterm_epsilon :
    proc_term Pepsilon
  (* alternative composition: left *)
  | pterm_alt_l P Q :
    proc_term P ->
    proc_term (Palt P Q)
  (* alternative composition: right *)
  | pterm_alt_r P Q :
    proc_term Q ->
    proc_term (Palt P Q)
  (* sequential composition *)
  | pterm_seq P Q :
    proc_term P ->
    proc_term Q ->
    proc_term (Pseq P Q)
  (* parallel composition *)
  | pterm_par P Q :
    proc_term P ->
    proc_term Q ->
    proc_term (Ppar P Q)
  (* left merge *)
  | pterm_lmerge P Q :
    proc_term P ->
    proc_term Q ->
    proc_term (Plmerge P Q)
  (* iteration *)
  | pterm_iter P :
    proc_term (Piter P).

Add Search Blacklist "proc_term_ind".

(** Below are a number of properties of [proc_term] related to the composition
    of the subject process. *)

Lemma pterm_seq_assoc :
  forall P Q R,
  proc_term (Pseq P (Pseq Q R)) <->
  proc_term (Pseq (Pseq P Q) R).
Proof.
  intros P Q R. split; intro H.
  (* [Pseq P (Pseq Q R)] terminates *)
  - inv H. clear H. inv H3. clear H3.
    by repeat constructor.
  (* [Pseq (Pseq P Q) R] terminates *)
  - inv H. clear H. inv H2. clear H2.
    by repeat constructor.
Qed.

Lemma pterm_seq_comm :
  forall P Q,
  proc_term (Pseq P Q) -> proc_term (Pseq Q P).
Proof.
  intros P Q H. inv H. clear H.
  by constructor.
Qed.

Lemma pterm_seq_delta :
  forall P,
  proc_term (Pseq Pdelta P) <-> proc_term Pdelta.
Proof.
  intros P.
  split; intro H; by inv H.
Qed.

Lemma pterm_alt_assoc :
  forall P Q R,
  proc_term (Palt P (Palt Q R)) <->
  proc_term (Palt (Palt P Q) R).
Proof.
  intros P Q R.
  split; intro H; inv H; clear H.
  (* [P] terminates *)
  - by repeat constructor.
  (* [Palt Q R] terminates *)
  - inv H1; clear H1.
    (* [Q] terminates *)
    + by apply pterm_alt_l, pterm_alt_r.
    (* [R] terminates *)
    + by apply pterm_alt_r.
  (* [Palt P Q] terminates *)
  - inv H1; clear H1.
    (* [P] terminates *)
    + by apply pterm_alt_l.
    (* [Q] terminates *)
    + by apply pterm_alt_r, pterm_alt_l.
  (* [R] terminates *)
  - by repeat apply pterm_alt_r.
Qed.

Lemma pterm_alt_comm :
  forall P Q,
  proc_term (Palt P Q) -> proc_term (Palt Q P).
Proof.
  intros P Q H. inv H; by constructor.
Qed.

Lemma pterm_alt_dist :
  forall P Q R,
  proc_term (Pseq (Palt P Q) R) <->
  proc_term (Palt (Pseq P R) (Pseq Q R)).
Proof.
  intros P Q R. split; intro H.
  (* left to right *)
  - inv H; clear H.
    (* [Palt P Q] and [R] both terminate *)
    + inv H2; clear H2.
      (* [P] and [R] terminate *)
      * by apply pterm_alt_l, pterm_seq.
      (* [Q] and [R] terminate *)
      * by apply pterm_alt_r, pterm_seq.
  (* right to left *)
  - inv H; clear H.
    (* [Pseq P R] terminates *)
    + inv H1; clear H1.
      apply pterm_seq; auto. by apply pterm_alt_l.
    (* [Pseq Q R] terminates *)
    + inv H1; clear H1.
      apply pterm_seq; auto. by apply pterm_alt_r.
Qed.

Lemma pterm_alt_delta :
  forall P,
  proc_term (Palt P Pdelta) <-> proc_term P.
Proof.
  intros P. split; intro H.
  (* left to right *)
  - inv H. clear H. by inv H1.
  (* right to left *)
  - by constructor.
Qed.

Lemma pterm_alt_idemp :
  forall P,
  proc_term (Palt P P) <-> proc_term P.
Proof.
  intros P. split; intro H.
  (* left to right *)
  - by inv H.
  (* right to left *)
   - by constructor.
Qed.

Lemma pterm_par_assoc :
  forall P Q R,
  proc_term (Ppar P (Ppar Q R)) <-> proc_term (Ppar (Ppar P Q) R).
Proof.
  intros P Q R. split; intro H.
  (* right to left *)
  - inv H. clear H. inv H3. clear H3.
    by repeat constructor.
  (* right to left *)
  - inv H. clear H. inv H2. clear H2.
    by repeat constructor.
Qed.

Lemma pterm_par_comm :
  forall P Q,
  proc_term (Ppar P Q) <-> proc_term (Ppar Q P).
Proof.
  intros P Q.
  split; intro H; inv H; by constructor.
Qed.

Lemma pterm_par_unfold :
  forall P Q,
  proc_term (Ppar P Q) <->
  proc_term (Palt (Plmerge P Q) (Plmerge Q P)).
Proof.
  intros P Q. split; intro H.
  (* left to right *)
  - inv H. clear H. by repeat constructor.
  (* right to left *)
  - inv H; inv H1; by repeat constructor.
Qed.

Lemma pterm_par_epsilon :
  forall P,
  proc_term (Ppar Pepsilon P) <-> proc_term P.
Proof.
  intro P. split; intro H.
  (* left to right *)
  - by inv H.
  (* right to left *)
  - by repeat constructor.
Qed.

Lemma pterm_par_delta :
  forall P,
  proc_term (Ppar P Pdelta) <-> proc_term (Pseq P Pdelta).
Proof.
  intros P.
  split; intro H; inv H; inv H3.
Qed.

Lemma pterm_lmerge_symm :
  forall P Q,
  proc_term (Plmerge P Q) -> proc_term (Plmerge Q P).
Proof.
  intros P Q H. inv H. clear H.
  by constructor.
Qed.

Lemma pterm_lmerge_delta :
  forall P,
  proc_term (Plmerge Pdelta P) <-> proc_term Pdelta.
Proof.
  intro P. split; intro H; inv H.
Qed.

Lemma pterm_lmerge_epsilon :
  proc_term (Plmerge Pepsilon Pdelta) <-> proc_term Pdelta.
Proof.
  split; intro H; inv H.
Qed.

Lemma pterm_lmerge_act_epsilon :
  forall a P,
  proc_term (Plmerge Pepsilon (Pseq (Pact a) P)) <->
  proc_term Pdelta.
Proof.
  intros a P.
  split; intro H; inv H. clear H.
  inv H3. clear H3. inv H1.
Qed.

Lemma pterm_lmerge_act :
  forall a P,
  proc_term (Plmerge (Pact a) P) <->
  proc_term (Pseq (Pact a) P).
Proof.
  intros a P.
  split; intro H; inv H; inv H2.
Qed.

Lemma pterm_lmerge_double_epsilon :
  proc_term (Plmerge Pepsilon Pepsilon) <->
  proc_term Pepsilon.
Proof.
  split; intro H; inv H.
  by constructor.
Qed.

Lemma pterm_lmerge_alt_epsilon :
  forall P Q,
  proc_term (Plmerge Pepsilon (Palt P Q)) <->
  proc_term (Palt (Plmerge Pepsilon P) (Plmerge Pepsilon Q)).
Proof.
  intros P S.
  split; intro H; inv H; clear H.
  (* [Palt P S] terminates *)
  - inv H3; by repeat constructor.
  (* [Plmerge Pepsilon P] terminates *)
  - inv H1. clear H1. by repeat constructor.
  (* [Plmerge Pepsilon S] terminates *)
  - inv H1. clear H1. by repeat constructor.
Qed.

Lemma pterm_lmerge_alt :
  forall P Q R,
  proc_term (Plmerge (Palt P Q) R) <->
  proc_term (Palt (Plmerge P R) (Plmerge Q R)).
Proof.
  intros P Q R.
  split; intro H; inv H; clear H.
  (* [Palt P Q] and [R] terminate *)
  - inv H2; by repeat constructor.
  (* [Plmerge P R] terminates *)
  - inv H1. clear H1. by repeat constructor.
  (* [Plmerge Q R] terminates *)
  - inv H1. clear H1. by repeat constructor.
Qed.

Lemma pterm_lmerge_par :
  forall P Q R,
  proc_term (Plmerge (Plmerge P Q) R) <->
  proc_term (Plmerge P (Ppar Q R)).
Proof.
  intros P Q R.
  split; intro H; inv H; clear H.
  (* [Plmerge P Q] and [R] both terminate *)
  - inv H2. clear H2. by repeat constructor.
  (* [P] and [Ppar Q R] both terminate *)
  - inv H3. clear H3. by repeat constructor.
Qed.

Lemma pterm_lmerge_delta_r :
  forall P,
  proc_term (Plmerge P Pdelta) <->
  proc_term (Pseq P Pdelta).
Proof.
  intro P.
  split; intro H; inv H; inv H3.
Qed.


(** *** Operational semantics *)

(** The operational semantics is defined as a small-step reduction
    relation labelled with action names. The transition rules are mostly standard.
    The rule [pstep_act] updates the process store according to the state change
    described by the actions' contract. *)

Inductive proc_sos : Proc -> ProcStore -> ActLabel -> Proc -> ProcStore -> Prop :=
  (* action invocation *)
  | pstep_act a ps1 ps2:
    pbexpr_denot (guard a) ps1 = true ->
    pbexpr_denot (effect a) ps2 = true ->
    proc_sos (Pact a) ps1 a Pepsilon ps2
  (* sequential, left *)
  | pstep_seq_l P Q a ps P' ps' :
    proc_sos P ps a P' ps' ->
    proc_sos (Pseq P Q) ps a (Pseq P' Q) ps'
  (* sequential, right *)
  | pstep_seq_r P Q a ps Q' ps' :
    proc_term P ->
    proc_sos Q ps a Q' ps' ->
    proc_sos (Pseq P Q) ps a Q' ps'
  (* choice, left *)
  | pstep_alt_l P Q a ps P' ps' :
    proc_sos P ps a P' ps' ->
    proc_sos (Palt P Q) ps a P' ps'
  (* choice, right *)
  | pstep_alt_r P Q a ps Q' ps' :
    proc_sos Q ps a Q' ps' ->
    proc_sos (Palt P Q) ps a Q' ps'
  (* parallel, left *)
  | pstep_par_l P Q a ps P' ps' :
    proc_sos P ps a P' ps' ->
    proc_sos (Ppar P Q) ps a (Ppar P' Q) ps'
  (* parallel, right *)
  | pstep_par_r P Q a ps Q' ps' :
    proc_sos Q ps a Q' ps' ->
    proc_sos (Ppar P Q) ps a (Ppar P Q') ps'
  (* left merge *)
  | pstep_lmerge P Q a ps P' ps' :
    proc_sos P ps a P' ps' ->
    proc_sos (Plmerge P Q) ps a (Ppar P' Q) ps'
  (* iteration *)
  | pstep_iter_l P a ps P' ps' :
    proc_sos P ps a P' ps' ->
    proc_sos (Piter P) ps a (Pseq P' (Piter P)) ps'.

Add Search Blacklist "proc_sos_ind".

Lemma psos_alt_idemp :
  forall P ps a P' ps',
  proc_sos (Palt P P) ps a P' ps' <->
  proc_sos P ps a P' ps'.
Proof.
  intros ?????. split; intro H.
  (* left to right *)
  - by inv H.
  (* right to left *)
  - by constructor.
Qed.

Lemma psos_par_comm :
  forall P Q ps a P' Q' ps',
  proc_sos (Ppar P Q) ps a (Ppar P' Q') ps' ->
  proc_sos (Ppar Q P) ps a (Ppar Q' P') ps'.
Proof.
  intros ??????? H.
  inv H; by constructor.
Qed.

Lemma proc_sos_act_agree :
  forall P ps a Q ps1 ps2,
  pstore_agree (act_fv a) ps1 ps2 ->
  proc_sos P ps a Q ps1 ->
  proc_sos P ps a Q ps2.
Proof.
  induction P; intros ps a' Q ps1 ps2 AGR1 H1; vauto.
  (* deadlock step *)
  - inv H1.
  (* epsilon step *)
  - inv H1.
  (* action step *)
  - inv H1. clear H1. constructor; vauto.
    rewrite <- pbexpr_agree with (ps1 := ps1)(ps2 := ps2); vauto.
    red. intros x IN1. apply AGR1. unfold act_fv.
    apply in_or_app. by right.
  (* sequential composition *)
  - inv H1; clear H1.
    + apply IHP1 with (ps2 := ps2) in H6; vauto.
    + apply IHP2 with (ps2 := ps2) in H7; vauto.
  (* choice *)
  - inv H1; clear H1.
    + apply IHP1 with (ps2 := ps2) in H6; vauto.
    + apply IHP2 with (ps2 := ps2) in H6; vauto.
  (* parallel composition *)
  - inv H1; clear H1.
    + apply IHP1 with (ps2 := ps2) in H6; vauto.
    + apply IHP2 with (ps2 := ps2) in H6; vauto.
  (* left-merge *)
  - inv H1; clear H1.
    apply IHP1 with (ps2 := ps2) in H6; vauto.
  (* iteration *)
  - inv H1; clear H1.
    apply IHP with (ps2 := ps2) in H0; vauto.
Qed.


(** ** Bisimulation *)

(** This section defines _bisimulation_, shows that bisimilarity is an
    equivalence relation, and shows that bisimulation equivalence is a _congruence_. *)

(** The definition of bisimulation is slightly non-standard in the way process
    stores are handled. This is because the operational semantics describes state updates
    in an abstract way (using action contracts), and bisimulation needs to
    cope with this. Besides, a standard definition would not be a congruence w.r.t.
    parallel composition. *)

CoInductive proc_bisim : relation Proc :=
  | pc_bisim P Q :
      (* right direction: [P] simulates [Q] *)
      (forall ps a P' ps' (STEP: proc_sos P ps a P' ps'),
        exists Q', proc_sos Q ps a Q' ps' /\ proc_bisim P' Q') /\
      (* left direction: [Q] simulates [P] *)
      (forall ps a Q' ps' (STEP: proc_sos Q ps a Q' ps'),
        exists P', proc_sos P ps a P' ps' /\ proc_bisim P' Q') /\
      (* termination: [P] can terminate iff [Q] can terminate *)
      (proc_term P <-> proc_term Q) ->
    proc_bisim P Q.

Notation "P ≃ Q" := (proc_bisim P Q) (at level 80).

(** Bisimilarity is an equivalence relation. *)

Instance proc_bisim_refl :
  Reflexive proc_bisim.
Proof.
  cofix.
  intro P. constructor.
  repeat split; vauto.
Qed.

Hint Resolve proc_bisim_refl.

Instance proc_bisim_symm :
  Symmetric proc_bisim.
Proof.
  cofix.
  intros P Q H. constructor.
  inv H. clear H. destruct H0 as (H1 & H2 & H3 & H4).
  repeat split; vauto.
  (* left process simulates right process *)
  - intros ps a Q' ps' H5.
    apply H2 in H5. destruct H5 as (P' & H5 & H6).
    exists P'. split; auto.
  (* right process simulates left process *)
  - intros ps a P' ps' H5.
    apply H1 in H5. destruct H5 as (Q' & H5 & H6).
    exists Q'. split; auto.
Qed.

Hint Resolve proc_bisim_symm.

Instance proc_bisim_trans :
  Transitive proc_bisim.
Proof.
  cofix.
  intros P Q R H1 H2. constructor.
  inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
  inv H2. clear H2. destruct H as (K5 & K6 & K7 & K8).
  repeat split; vauto.
  (* left process simulates right process *)
  - intros ps a P' ps' H11.
    apply K1 in H11. destruct H11 as (Q' & H11 & H12).
    apply K5 in H11. destruct H11 as (R' & H11 & H13).
    exists R'. split; auto.
    by apply proc_bisim_trans with Q'.
  (* right process simulates left process *)
  - intros ps a R' ps' H11.
    apply K6 in H11. destruct H11 as (Q' & H11 & H12).
    apply K2 in H11. destruct H11 as (P' & H11 & H13).
    exists P'. split; auto.
    by apply proc_bisim_trans with Q'.
  (* left process can terminate implies right process can terminate *)
  - intro H11. by apply K7, K3.
  (* right process can terminate implies left process can terminate *)
  - intro H11. by apply K4, K8.
Qed.

Instance proc_bisim_equiv :
  Equivalence proc_bisim.
Proof.
  split; intuition.
Qed.

Lemma proc_bisim_term :
  forall P1 P2,
  proc_bisim P1 P2 -> proc_term P1 -> proc_term P2.
Proof.
  intros P1 P2 H1 H2.
  inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
  by apply K3.
Qed.

Add Parametric Morphism : proc_term
  with signature proc_bisim ==> iff
    as proc_term_mor.
Proof.
  intros P Q H1. split; intro H2.
  apply proc_bisim_term with P; auto.
  apply proc_bisim_term with Q; auto.
Qed.

Lemma proc_bisim_alt_idemp :
  forall P,
  proc_bisim (Palt P P) P.
Proof.
  intro P. constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' STEP.
    inv STEP; by exists P'.
  (* right process simulates left process *)
  - intros ps a P' ps' STEP.
    exists P'. intuition. by constructor.
  (* left process can terminate implies right process can terminate *)
  - intro H. by rewrite pterm_alt_idemp in H.
  (* right process can terminate implies left process can terminate *)
  - intro H. by constructor.
Qed.


(** *** Congruence *)

(** Bisimulation equivalence is a _congruence_ with respect to all process
    algebraic connectives. *)

Theorem proc_bisim_seq_cong :
  forall P1 P2 Q1 Q2,
  proc_bisim P1 P2 ->
  proc_bisim Q1 Q2 ->
  proc_bisim (Pseq P1 Q1) (Pseq P2 Q2).
Proof.
  cofix.
  intros P1 P2 Q1 Q2 H1 H2.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    (* [P1] makes a step *)
    + rename P'0 into P1'.
      inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
      apply K1 in H7. destruct H7 as (P2' & H7 & H8).
      exists (Pseq P2' Q2). split; vauto.
      by apply proc_bisim_seq_cong.
    (* [P1] terminates and [Q1] makes a step *)
    + rename P' into Q1'.
      inv H2. clear H2. destruct H as (K1 & K2 & K3 & K4).
      apply K1 in H8. destruct H8 as (Q2' & H8 & H9).
      exists Q2'. split; vauto.
      constructor; vauto.
      inv H1. clear H1. destruct H as (J1 & J2 & J3 & J4).
      by apply J3.
  (* right process simulates left process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    (* [P2] makes a step *)
    + rename P'0 into P2'.
      inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
      apply K2 in H7.
      destruct H7 as (P1' & H7 & H8).
      exists (Pseq P1' Q1). split; auto.
      by constructor.
    (* [P2] terminates and [Q2] makes a step *)
    + rename P' into Q2'.
      inv H2. clear H2. destruct H as (K1 & K2 & K3 & K4).
      apply K2 in H8. destruct H8 as (Q1' & H8 & H9).
      exists Q1'. split; auto.
      constructor; auto.
      inv H1. clear H1. destruct H as (J1 & J2 & J3 & J4).
      by apply J4.
  (* left process can terminate implies right process can terminate *)
  - intro H. inv H. clear H. constructor.
    by rewrite <- H1.
    by rewrite <- H2.
  (* right process can terminate implies left process can terminate *)
  - intro H. inv H. clear H. constructor.
    by rewrite H1.
    by rewrite H2.
Qed.

Add Parametric Morphism : Pseq
  with signature proc_bisim ==> proc_bisim ==> proc_bisim
    as proc_seq_cong_mor.
Proof.
  intros P1 Q1 H1 P2 Q2 H2.
  by apply proc_bisim_seq_cong.
Qed.

Theorem proc_bisim_alt_cong :
  forall P1 P2 Q1 Q2,
  proc_bisim P1 P2 ->
  proc_bisim Q1 Q2 ->
  proc_bisim (Palt P1 Q1) (Palt P2 Q2).
Proof.
  intros P1 P2 Q1 Q2 H1 H2.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    (* [P1] makes a step *)
    + rename P' into P1'.
      inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
      apply K1 in H7. destruct H7 as (P2' & H7 & H8).
      exists P2'. split; auto.
      by apply pstep_alt_l.
    (* [Q1] makes a step *)
    + rename P' into Q1'.
      inv H2. clear H2. destruct H as (K1 & K2 & K3 & K4).
      apply K1 in H7. destruct H7 as (Q2' & H7 & H8).
      exists Q2'. split; auto.
      by apply pstep_alt_r.
  (* right process simulates left process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    (* [P2] makes a step *)
    + rename P' into P2'.
      inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
      apply K2 in H7. destruct H7 as (P1' & H7 & H8).
      exists P1'. split; auto.
      by apply pstep_alt_l.
    (* [Q2] makes a step *)
    + rename P' into Q2'.
      inv H2. clear H2. destruct H as (K1 & K2 & K3 & K4).
      apply K2 in H7. destruct H7 as (Q1' & H7 & H8).
      exists Q1'. split; auto.
      by apply pstep_alt_r.
  (* left process can terminate implies right process can terminate *)
  - intro H. inv H; clear H.
    (* [P1] terminates *)
    + apply pterm_alt_l. by rewrite <- H1.
    (* [Q1] terminates *)
    + apply pterm_alt_r. by rewrite <- H2.
  (* right process can terminate implies left process can terminate *)
  - intro H. inv H; clear H.
    (* [P2] terminates *)
    + apply pterm_alt_l. by rewrite H1.
    (* [Q2] terminates *)
    + apply pterm_alt_r. by rewrite H2.
Qed.

Add Parametric Morphism : Palt
  with signature proc_bisim ==> proc_bisim ==> proc_bisim
    as proc_alt_cong_mor.
Proof.
  intros P1 Q1 H1 P2 Q2 H2.
  by apply proc_bisim_alt_cong.
Qed.

Theorem proc_bisim_par_cong :
  forall P1 P2 Q1 Q2,
  proc_bisim P1 P2 ->
  proc_bisim Q1 Q2 ->
  proc_bisim (Ppar P1 Q1) (Ppar P2 Q2).
Proof.
  cofix.
  intros P1 P2 Q1 Q2 H1 H2.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    (* [P1] makes a step *)
    + rename P'0 into P1'.
      inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
      apply K1 in H7. destruct H7 as (P2' & H7 & H8).
      exists (Ppar P2' Q2). split; auto.
      by constructor.
    (* [Q1] makes a step *)
    + rename Q' into Q1'.
      inv H2. clear H2. destruct H as (K1 & K2 & K3 & K4).
      apply K1 in H7. destruct H7 as (Q2' & H7 & H8).
      exists (Ppar P2 Q2'). split; auto.
      by constructor.
  (* right process simulates left process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    (* [P2] makes a step *)
    + rename P'0 into P2'.
      inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
      apply K2 in H7. destruct H7 as (P1' & H7 & H8).
      exists (Ppar P1' Q1). split; auto.
      by constructor.
    (* [Q2] makes a step *)
    + rename Q' into Q2'.
      inv H2. clear H2. destruct H as (K1 & K2 & K3 & K4).
      apply K2 in H7. destruct H7 as (Q1' & H7 & H8).
      exists (Ppar P1 Q1'). split; auto.
      by constructor.
  (* left process can terminate implies right process can terminate *)
  - intro H. inv H. clear H. constructor.
    (* [P2] terminates *)
    + by rewrite <- H1.
    (* [Q2] terminates *)
    + by rewrite <- H2.
  (* right process can terminate implies left process can terminate *)
  - intro H. inv H. clear H. constructor.
    (* [P1] terminates *)
    + by rewrite H1.
    (* [Q1] terminates *)
    + by rewrite H2.
Qed.

Add Parametric Morphism : Ppar
  with signature proc_bisim ==> proc_bisim ==> proc_bisim
    as proc_par_cong_mor.
Proof.
  intros P1 Q1 H1 P2 Q2 H2.
  by apply proc_bisim_par_cong.
Qed.

Theorem proc_bisim_lmerge_cong :
  forall P1 P2 Q1 Q2,
  proc_bisim P1 P2 ->
  proc_bisim Q1 Q2 ->
  proc_bisim (Plmerge P1 Q1) (Plmerge P2 Q2).
Proof.
  intros P1 P2 Q1 Q2 H1 H2.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' STEP.
    inv STEP. clear STEP.
    rename P'0 into P1'.
    inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
    apply K1 in H7. destruct H7 as (P2' & H7 & H8).
    exists (Ppar P2' Q2). split; vauto.
    by rewrite H2, H8.
  (* right process simulates left process *)
  - intros ps a P' ps' STEP.
    inv STEP. clear STEP.
    rename P'0 into P2'.
    inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
    apply K2 in H7. destruct H7 as (P1' & H7 & H8).
    exists (Ppar P1' Q1). split; vauto.
    by rewrite H2, H8.
  (* left process can terminate implies right process can terminate *)
  - intro H. inv H. clear H. constructor.
    (* [P2] terminates *)
    + by rewrite <- H1.
    (* [P1] terminates *)
    + by rewrite <- H2.
  (* right process can terminate implies left process can terminate *)
  - intro H. inv H. clear H. constructor.
    (* [P1] terminates *)
    + by rewrite H1.
    (* [Q1] terminates *)
    + by rewrite H2.
Qed.

Add Parametric Morphism : Plmerge
  with signature proc_bisim ==> proc_bisim ==> proc_bisim
    as proc_lmerge_cong_mor.
Proof.
  intros P1 Q1 H1 P2 Q2 H2.
  by apply proc_bisim_lmerge_cong.
Qed.

Lemma proc_bisim_iter_seq_cong :
  forall P1 P2 Q1 Q2,
  proc_bisim P1 P2 ->
  proc_bisim Q1 Q2 ->
  proc_bisim (Pseq P1 (Piter Q1)) (Pseq P2 (Piter Q2)).
Proof.
  cofix.
  intros P1 P2 Q1 Q2 H1 H2.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    (* [P1] makes a step *)
    + rename P'0 into P1'.
      inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
      apply K1 in H7. destruct H7 as (P2' & H7 & H8).
      exists (Pseq P2' (Piter Q2)).
      split; auto. by constructor.
    (* [P1] terminates and [Piter Q1] makes a step *)
    + inv H8. clear H8. rename P'0 into Q1'.
      inv H2. destruct H as (K1 & K2 & K3 & K4).
      apply K1 in H0. destruct H0 as (Q2' & H0 & H0').
      exists (Pseq Q2' (Piter Q2)).
      split; auto. apply pstep_seq_r; vauto.
      inv H1. clear H1. destruct H as (J1 & J2 & J3 & J4).
      by apply J3.
  (* right process simulates left process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    (* [P2] makes a step *)
    + rename P'0 into P2'.
      inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
      apply K2 in H7. destruct H7 as (P1' & H7 & H8).
      exists (Pseq P1' (Piter Q1)).
      split; auto. by constructor.
    (* [Piter Q2] makes a step *)
    + inv H8. clear H8. rename P'0 into Q2'.
      inv H2. destruct H as (K1 & K2 & K3 & K4).
      apply K2 in H0. destruct H0 as (Q1' & H4 & H5).
      exists (Pseq Q1' (Piter Q1)).
      split; auto. apply pstep_seq_r; vauto.
      inv H1. clear H1. destruct H as (J1 & J2 & J3 & J4).
      by apply J4.
  (* left process can terminate implies right process can terminate *)
  - intro H. inv H. clear H. constructor; vauto.
    by rewrite <- H1.
  (* right process can terminate implies left process can terminate *)
  - intro H. inv H. clear H. constructor; vauto.
    by rewrite H1.
Qed.

Theorem proc_bisim_iter_cong :
  forall P Q,
  proc_bisim P Q -> proc_bisim (Piter P) (Piter Q).
Proof.
  intros P Q H.
  constructor. repeat split; vauto.
  (* left process simulates right process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    rename P'0 into P'.
    inv H. clear H. destruct H0 as (K1 & K2 & K3 & K4).
    apply K1 in H1. destruct H1 as (Q' & H1 & H2).
    exists (Pseq Q' (Piter Q)).
    split; vauto.
    by apply proc_bisim_iter_seq_cong.
  (* right process simulates left process *)
  - intros ps a P' ps' STEP.
    inv STEP; clear STEP.
    rename P'0 into Q'.
    inv H. clear H. destruct H0 as (K1 & K2 & K3 & K4).
    apply K2 in H1. destruct H1 as (P' & H1 & H2).
    exists (Pseq P' (Piter P)).
    split; vauto.
    by apply proc_bisim_iter_seq_cong.
Qed.

Add Parametric Morphism : Piter
  with signature proc_bisim ==> proc_bisim
    as proc_iter_cong_mor.
Proof.
  intros P Q H.
  by apply proc_bisim_iter_cong.
Qed.


(** ** Soundness of axiomatisation *)

(** This section proves soundness of the axiomatisation
    of the process algebra theory. *)

Theorem proc_A1 :
  forall P Q,
  proc_bisim (Palt P Q) (Palt Q P).
Proof.
  intros P Q.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; exists P'; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H; exists P'; vauto.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_alt_comm.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_alt_comm.
Qed.

Theorem proc_A2 :
  forall P Q R,
  proc_bisim (Palt P (Palt Q R)) (Palt (Palt P Q) R).
Proof.
  intros P Q R.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [P] makes a step *)
    + exists P'. split; vauto.
    (* [Palt Q R] makes a step *)
    + inv H6; exists P'; split; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Palt P Q] makes a step *)
    + exists P'. inv H6; clear H6; split; vauto.
    (* [R] makes a step *)
    + exists P'. split; vauto.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_alt_assoc.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_alt_assoc.
Qed.

Theorem proc_A3 :
  forall P,
  proc_bisim (Palt P P) P.
Proof.
  intro P. apply proc_bisim_alt_idemp.
Qed.

Theorem proc_A4 :
  forall P Q R,
  proc_bisim (Pseq (Palt P Q) R) (Palt (Pseq P R) (Pseq Q R)).
Proof.
  intros P Q R.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Palt P Q] makes a step *)
    + rename P'0 into P'.
      inv H6; exists (Pseq P' R); split; vauto.
    (* [R] makes a step *)
    + rename P' into R'.
      inv H2; exists R'; split; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Pseq P R] makes a step *)
    + inv H6; clear H6.
      (* [P] makes a step *)
      * rename P'0 into P'.
        exists (Pseq P' R). split; vauto.
      (* [P] terminates and [R] makes a step *)
      * exists P'. split; vauto.
    (* [Pseq Q R] makes a step *)
    + inv H6; clear H6.
      (* [Q] makes a step *)
      * rename P'0 into Q'.
        exists (Pseq Q' R). split; vauto.
      (* [Q] terminates and [R] makes a step *)
      * exists P'. split; vauto.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_alt_dist.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_alt_dist.
Qed.

Theorem proc_A5 :
  forall P Q R,
  proc_bisim (Pseq P (Pseq Q R)) (Pseq (Pseq P Q) R).
Proof.
  cofix.
  intros P Q R.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [P] makes a step *)
    + rename P'0 into P'.
      exists (Pseq (Pseq P' Q) R). split; vauto.
    (* [P] terminates and [Pseq Q R] makes a step *)
    + inv H7; clear H7.
      (* [Q] makes a step *)
      * rename P'0 into Q'.
        exists (Pseq Q' R). split; vauto.
      (* [P] and [Q] both terminate and [R] makes a step *)
      * rename P' into R'.
        exists R'. split; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Pseq P Q] makes a step *)
    + inv H6; clear H6.
      (* [P] makes a step *)
      * exists (Pseq P' (Pseq Q R)). split; vauto.
      (* [P] terminates and [Q] makes a step *)
      * rename P'0 into Q'.
        exists (Pseq Q' R). split; vauto.
    (* [Pseq P Q] terminates and [R] makes a step *)
    + rename P' into R'. inv H2. clear H2.
      exists R'. split; vauto.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_seq_assoc.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_seq_assoc.
Qed.

Theorem proc_A6 :
  forall P,
  proc_bisim (Palt P Pdelta) P.
Proof.
  intros P.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H; vauto.
    exists P'. split; vauto. by inv H6.
  (* right process simulates left process *)
  - intros ps a P' ps' H.
    exists P'. split; vauto.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_alt_delta.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_alt_delta.
Qed.

Theorem proc_A7 :
  forall P,
  proc_bisim (Pseq Pdelta P) Pdelta.
Proof.
  intros P.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Pdelta] makes a step (contradiction) *)
    + by inv H6.
    (* [Pdelta] terminates (contradiction) *)
    + by inv H2.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_seq_delta.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_seq_delta.
Qed.

Theorem proc_A8 :
  forall P,
  proc_bisim (Pseq P Pepsilon) P.
Proof.
  cofix.
  intros P. constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [P] makes a step *)
    + rename P'0 into P'.
      exists P'. split; vauto.
    (* [Pepsilon] makes a step (contradiction) *)
    + by inv H7.
  (* right process simulates left process *)
  - intros ps a P' ps' H.
    exists (Pseq P' Pepsilon). split; vauto.
  (* left process can terminate implies right process can terminate *)
  - intro H. inv H.
  (* right process can terminate implies left process can terminate *)
  - intro H. vauto.
Qed.

Theorem proc_A9 :
  forall P,
  proc_bisim (Pseq Pepsilon P) P.
Proof.
  cofix.
  intros P. constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Pepsilon] makes a step (contradiction) *)
    + by inv H6.
    (* [P] makes a step *)
    + exists P'. split; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H.
    exists P'. split; vauto.
  (* left process can terminate implies right process can terminate *)
  - intro H. inv H.
  (* right process can terminate implies left process can terminate *)
  - intro H. vauto.
Qed.

Theorem proc_M1:
  forall P Q,
  proc_bisim (Ppar P Q) (Ppar Q P).
Proof.
  cofix.
  intros P Q. constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [P] makes a step *)
    + rename P'0 into P'.
      exists (Ppar Q P'). split; vauto.
    (* [Q] makes a step *)
    + exists (Ppar Q' P). split; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Q] makes a step *)
    + rename P'0 into Q'.
      exists (Ppar P Q'). split; vauto.
    (* [P] makes a step *)
    + rename Q' into P'.
      exists (Ppar P' Q). split; vauto.
  (* left process can terminate implies right process can terminate *)
  - intro H. inv H. clear H. vauto.
  (* right process can terminate implies left process can terminate *)
  - intro H. inv H. clear H. vauto.
Qed.

Theorem proc_M2 :
  forall P Q R,
  proc_bisim (Ppar P (Ppar Q R)) (Ppar (Ppar P Q) R).
Proof.
  cofix.
  intros P Q R. constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [P] makes a step *)
    + rename P'0 into P'.
      exists (Ppar (Ppar P' Q) R).
      split; vauto.
    (* [Ppar Q R] makes a step *)
    + inv H6; clear H6.
      (* [Q] makes a step *)
      * rename P' into Q'.
        exists (Ppar (Ppar P Q') R). split; vauto.
      (* [R] makes a step *)
      * rename Q'0 into R'.
        exists (Ppar (Ppar P Q) R'). split; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Ppar P Q] makes a step *)
    + inv H6; clear H6.
      (* [P] makes a step *)
      * exists (Ppar P' (Ppar Q R)). split; vauto.
      (* [Q] makes a step *)
      * exists (Ppar P (Ppar Q' R)). split; vauto.
    (* [R] makes a step *)
    + rename Q' into R'.
      exists (Ppar P (Ppar Q R')). split; vauto.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_par_assoc.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_par_assoc.
Qed.

Theorem proc_M3 :
  forall P Q,
  proc_bisim (Ppar P Q) (Palt (Plmerge P Q) (Plmerge Q P)).
Proof.
  intros P Q.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [P] makes a step *)
    + rename P'0 into P'.
      exists (Ppar P' Q). split; vauto.
    (* [Q] makes a step *)
    + exists (Ppar Q' P). split; vauto.
      apply proc_M1.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Plmerge P Q] makes a step *)
    + inv H6; clear H6. rename P'0 into P'.
      exists (Ppar P' Q). split; vauto.
    (* [Plmerge Q P] makes a step *)
    + inv H6; clear H6. rename P'0 into Q'.
      exists (Ppar P Q'). split; vauto.
      apply proc_M1.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_par_unfold.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_par_unfold.
Qed.

Theorem proc_M4 :
  forall P,
  proc_bisim (Ppar Pepsilon P) P.
Proof.
  cofix.
  intros P. constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [Pepsilon] makes a step (contradiction) *)
    + by inv H6.
    (* [P] makes a step *)
    + rename Q' into P'. exists P'. split; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H.
    exists (Ppar Pepsilon P'). split; vauto.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_par_epsilon.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_par_epsilon.
Qed.

Theorem proc_M5 :
  forall P,
  proc_bisim (Ppar P Pdelta) (Pseq P Pdelta).
Proof.
  cofix.
  intros P. constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [P] makes a step *)
    + rename P'0 into P'.
      exists (Pseq P' Pdelta). split; vauto.
    (* [Pdelta] makes a step (contradiction) *)
    + by inv H6.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [P] makes a step *)
    + rename P'0 into P'.
      exists (Ppar P' Pdelta). split; vauto.
    (* [Pdelta] makes a step (contradiction) *)
    + by inv H7.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_par_delta.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_par_delta.
Qed.

Theorem proc_ML1 :
  forall P,
  proc_bisim (Plmerge Pdelta P) Pdelta.
Proof.
  intros P.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H. clear H. by inv H6.
  (* right process simulates left process *)
  - intros ps a P' ps' H. by inv H.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_lmerge_delta.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_lmerge_delta.
Qed.

Theorem proc_ML2 :
  proc_bisim (Plmerge Pepsilon Pdelta) Pdelta.
Proof.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H. clear H. by inv H6.
  (* right process simulates left process *)
  - intros ps a P' ps' H. by inv H.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_lmerge_epsilon.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_lmerge_epsilon.
Qed.

Theorem proc_ML3 :
  forall a P,
  proc_bisim (Plmerge Pepsilon (Pseq (Pact a) P)) Pdelta.
Proof.
  intros a P.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a' P' ps' H. inv H. clear H. by inv H6.
  (* right process simulates left process *)
  - intros ps a' P' ps' H. by inv H.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_lmerge_act_epsilon.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_lmerge_act_epsilon.
Qed.

Theorem proc_ML4 :
  forall a P,
  proc_bisim (Plmerge (Pact a) P) (Pseq (Pact a) P).
Proof.
  intros a P.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a' P' ps' H. inv H. clear H.
    rename P'0 into P'.
    exists (Pseq P' P). split; vauto.
    inv H6. transitivity P.
    (* [Ppar Pepsilon P] is bisimilar to [P] *)
    + by apply proc_M4.
    (* [P] is bisimilar to [Pseq Pepsilon P] *)
    + symmetry. by apply proc_A9.
  (* right process simulates left process *)
  - intros ps a' P' ps' H. inv H; clear H.
    (* [Pact a] makes a step *)
    + rename P'0 into P'.
      exists (Ppar P' P). split; vauto.
      inv H6. transitivity P.
      (* [P] is bisimilar to [Pseq Pepsilon P] *)
      * by apply proc_M4.
      (* [P] is bisimilar to [Pseq Pepsilon P] *)
      * symmetry. apply proc_A9.
    (* [Pact a] terminates (contradiction) and [P] makes a step *)
    + by inv H2.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_lmerge_act.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_lmerge_act.
Qed.

Theorem proc_ML5 :
  proc_bisim (Plmerge Pepsilon Pepsilon) Pepsilon.
Proof.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a' P' ps' H. inv H. clear H. by inv H6.
  (* right process simulates left process *)
  - intros ps a' P' ps' H. by inv H.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_lmerge_double_epsilon.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_lmerge_double_epsilon.
Qed.

Theorem proc_ML6 :
  forall P Q,
  proc_bisim (Plmerge Pepsilon (Palt P Q)) (Palt (Plmerge Pepsilon P) (Plmerge Pepsilon Q)).
Proof.
  intros P Q.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a' P' ps' H. inv H. clear H. by inv H6.
  (* right process simulates left process *)
  - intros ps a' P' ps' H. inv H; inv H6; inv H7.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_lmerge_alt_epsilon.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_lmerge_alt_epsilon.
Qed.

Theorem proc_ML7 :
  forall P Q R,
  proc_bisim (Plmerge (Palt P Q) R) (Palt (Plmerge P R) (Plmerge Q R)).
Proof.
  intros P Q R.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H. clear H.
    inv H6; clear H6.
    (* [P] makes a step *)
    + rename P'0 into P'.
      exists (Ppar P' R). split; vauto.
    (* [Q] makes a step *)
    + rename P'0 into Q'.
      exists (Ppar Q' R). split; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H.
    inv H; clear H. 
    (* [Plmerge P R] makes a step *)
    + inv H6; clear H6.
      rename P'0 into P'.
      exists (Ppar P' R). split; vauto.
    (* [Plmerge Q R] makes a step *)
    + inv H6; clear H6.
      rename P'0 into Q'.
      exists (Ppar Q' R). split; vauto.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_lmerge_alt.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_lmerge_alt.
Qed.

Theorem proc_ML8 :
  forall P Q R,
  proc_bisim (Plmerge (Plmerge P Q) R) (Plmerge P (Ppar Q R)).
Proof.
  intros P Q R.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H.
    inv H. clear H. inv H6.
    exists (Ppar P' (Ppar Q R)).
    split; vauto. symmetry. by apply proc_M2.
  (* right process simulates left process *)
  - intros ps a P' ps' H.
    inv H. clear H. rename P'0 into P'.
    exists (Ppar (Ppar P' Q) R). split; vauto.
    symmetry. by apply proc_M2.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_lmerge_par.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_lmerge_par.
Qed.

Theorem proc_ML9 :
  forall P,
  proc_bisim (Plmerge P Pdelta) (Pseq P Pdelta).
Proof.
  intros P.
  constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H. clear H.
    rename P'0 into P'. exists (Pseq P' Pdelta).
    split; vauto. by apply proc_M5.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H; clear H.
    (* [P] makes a step *)
    + rename P'0 into P'.
      exists (Ppar P' Pdelta).
      split; vauto. by apply proc_M5.
    (* [Pdelta] makes a step (contradiction) *)
    + by inv H7.
  (* left process can terminate implies right process can terminate *)
  - apply pterm_lmerge_delta_r.
  (* right process can terminate implies left process can terminate *)
  - apply pterm_lmerge_delta_r.
Qed.

Theorem proc_M10 :
  forall a P Q,
  proc_bisim (Plmerge (Pseq (Pact a) P) Q) (Pseq (Pact a) (Ppar P Q)).
Proof.
  intros a P Q. constructor. repeat split.
  (* left process simulates right process *)
  - intros ps a' P' ps' H. exists (Pseq Pepsilon (Ppar P Q)).
    inv H. clear H. inv H6; clear H6.
    + inv H5. clear H5. split; vauto.
      by repeat rewrite proc_A9.
    + inv H1.
  (* right process simulates left process *)
  - intros ps a' P' ps' H. exists (Ppar (Pseq Pepsilon P) Q).
    inv H; clear H.
    + inv H6. clear H6. split; vauto.
      * by repeat constructor.
      * by repeat rewrite proc_A9.
    + inv H2.
  (* termination cases *)
  - intro H. inv H. clear H. inv H2. clear H2. inv H1.
  - intro H. inv H. clear H. inv H2.
Qed.

Theorem proc_R1 :
  forall P : Proc,
  proc_bisim (Piter P) (Palt (Pseq P (Piter P)) Pepsilon).
Proof.
  intro P.
  constructor. repeat split; vauto.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H. clear H.
    rename P'0 into P'.
    exists (Pseq P' (Piter P)). split; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' H.
    inv H; clear H.
    (* [Pseq P (Piter P)] makes a step *)
    + inv H6; clear H6.
      (* [P] makes a step *)
      * rename P'0 into P'.
        exists (Pseq P' (Piter P)). split; vauto.
      (* [P] terminates and [Piter P] makes a step *)
      * inv H7. clear H7. rename P'0 into P'.
        exists (Pseq P' (Piter P)). split; vauto.
    (* [Pepsilon] makes a step (contradiction) *)
    + by inv H6.
Qed.

Lemma proc_seq_R2 :
  forall P Q R : Proc,
  proc_bisim (Pseq P (Piter (Palt Q R))) (Pseq (Pseq P (Piter Q)) (Piter (Pseq R (Piter Q)))).
Proof.
  cofix.
  intros P Q R. repeat split; vauto.
  (* left process simulates right process *)
  - intros ps a P' ps' STEP. inv STEP; clear STEP.
    + rename P'0 into P'.
      exists (Pseq (Pseq P' (Piter Q)) (Piter (Pseq R (Piter Q)))).
      split; vauto.
    + inv H6. clear H6. inv H0; clear H0.
      * rename P'0 into Q'.
        exists (Pseq (Pseq Q' (Piter Q)) (Piter (Pseq R (Piter Q)))).
        split; vauto. constructor. apply pstep_seq_r; auto.
        by constructor.
      * rename P'0 into R'.
        exists (Pseq (Pseq R' (Piter Q)) (Piter (Pseq R (Piter Q)))).
        split; vauto. apply pstep_seq_r; vauto.
  (* right process simulates left process *)
  - intros ps a P' ps' STEP. inv STEP; clear STEP.
    + inv H5; clear H5.
      * exists (Pseq P' (Piter (Palt Q R))). split; vauto.
      * inv H7; clear H7. rename P' into Q'.
        exists (Pseq Q' (Piter (Palt Q R))). split; vauto.
        apply pstep_seq_r; auto. apply pstep_iter_l.
        by apply pstep_alt_l.
    + inv H1. clear H1 H3. inv H6; clear H6; vauto.
      inv H0; clear H0.
      * rename P' into R'. exists (Pseq R' (Piter (Palt Q R))).
        split; vauto. apply pstep_seq_r; auto.
        by apply pstep_iter_l, pstep_alt_r.
      * inv H8; clear H8. rename P' into Q'.
        exists (Pseq Q' (Piter (Palt Q R))). split; vauto.
        apply pstep_seq_r; auto. by apply pstep_iter_l, pstep_alt_l.
  (* termination conditions *)
  - intros TERM. inv TERM. clear H2. constructor; vauto.
  - intros TERM. inv TERM. clear H2. inv H1. clear H3. constructor; vauto.
Qed.

Theorem proc_R2 :
  forall P Q : Proc,
  proc_bisim (Piter (Palt P Q)) (Pseq (Piter P) (Piter (Pseq Q (Piter P)))).
Proof.
  intros P Q. repeat split; vauto.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H. clear H.
    inv H1; clear H1; rename P'0 into P'.
    + exists (Pseq (Pseq P' (Piter P)) (Piter (Pseq Q (Piter P)))).
      split; vauto. apply proc_seq_R2.
    + rename P' into Q'.
      exists (Pseq (Pseq Q' (Piter P)) (Piter (Pseq Q (Piter P)))).
      split; vauto.
      * apply pstep_seq_r; vauto.
      * apply proc_seq_R2.
  (* right process simulates left process *)
  - intros ph a P' ps' STEP. inv STEP; clear STEP.
    + inv H5; vauto. clear H5.
      exists (Pseq P' (Piter (Palt P Q))). split; vauto.
      apply proc_seq_R2.
    + clear H1. inv H6. clear H6. inv H0; clear H0.
      * rename P' into Q'. exists (Pseq Q' (Piter (Palt P Q))).
        split; vauto. by apply proc_seq_R2.
      * inv H7; clear H7. exists (Pseq P' (Piter (Palt P Q))).
        split; vauto. by apply proc_seq_R2.
Qed.

Theorem proc_R3 :
  proc_bisim (Piter Pdelta) Pepsilon.
Proof.
  constructor. repeat split; vauto.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H. inv H1.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H.
Qed.

Theorem proc_R4 :
  proc_bisim (Piter Pepsilon) Pepsilon.
Proof.
  constructor. repeat split; vauto.
  (* left process simulates right process *)
  - intros ps a P' ps' H. inv H. inv H1.
  (* right process simulates left process *)
  - intros ps a P' ps' H. inv H.
Qed.

Close Scope Z_scope.
