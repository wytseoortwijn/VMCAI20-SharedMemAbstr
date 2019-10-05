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
Require Import QArith.
Require Import Qcanon.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.

Set Implicit Arguments.


(** * Soundness *)

(** ** Process validity *)

CoInductive proc_valid (b : ProcBoolExpr) : Proc -> ProcStore -> Prop :=
  | pv_cond P ps :
    (* termination condition *)
      (proc_term P -> pbexpr_denot b ps = true) /\
    (* progress condition *)
      (forall a P' ps', proc_sos P ps a P' ps' -> proc_valid b P' ps') ->
    proc_valid b P ps.

Theorem proc_valid_bisim :
  forall P Q b ps,
  proc_bisim P Q ->
  proc_valid b P ps ->
  proc_valid b Q ps.
Proof.
  cofix.
  intros P Q b ps H1 H2.
  constructor. split.
  (* termination *)
  - intro H3. inv H1. inv H2.
    destruct H as (K1 & K2 & K3 & K4).
    destruct H0 as (K5 & K6).
    by apply K5, K4.
  (* progress *)
  - intros a Q' ps' H3.
    inv H1. destruct H as (K1 & K2 & K3 & K4).
    apply K2 in H3. destruct H3 as (P' & H3 & H4).
    apply proc_valid_bisim with P'; auto.
    inv H2. destruct H as (H5 & H6).
    by apply H6 with a.
Qed.

Add Parametric Morphism : proc_valid
  with signature eq ==> proc_bisim ==> eq ==> iff
    as Pproc_valid_bisim_mor.
Proof.
  intros b P1 P2 H1 ps. intuition.
  - by apply proc_valid_bisim with P1.
  - apply proc_valid_bisim with P2; auto.
Qed.

Lemma proc_valid_alt :
  forall b P Q ps,
  proc_valid b (Palt P Q) ps ->
  proc_valid b P ps.
Proof.
  intros b P Q ps H1.
  inv H1. destruct H as (H2 & H3).
  constructor. split.
  (* termination *)
  - intro H4. apply H2. vauto.
  (* progress *)
  - intros a P' ps' H4.
    apply H3 with a. vauto.
Qed.

Lemma proc_valid_delta :
  forall b ps,
  proc_valid b Pdelta ps.
Proof.
  intros b ps.
  constructor. intuition inv H.
Qed.

Lemma proc_valid_epsilon :
  forall b ps,
  proc_valid b Pepsilon ps <->
  pbexpr_denot b ps = true.
Proof.
  intros b s. split; intro H1.
  (* left to right *)
  - inv H1. destruct H as (H2 & H3).
    apply H2. vauto.
  (* right to left *)
  - constructor. split; vauto.
    intros a P' ps' H2. inv H2.
Qed.


(** *** Process environment adequacy *)

Definition ProcEnv : Type := ProcLabel -> ProcBoolExpr * ProcBoolExpr.

Definition procenv_iden : ProcEnv := fun p : ProcLabel => (PBconst false, PBconst true).

Definition procenv_safe (env : ProcEnv) : Prop :=
  forall (p : ProcLabel)(ps : ProcStore),
  pbexpr_denot (fst (env p)) ps = true ->
  proc_valid (snd (env p)) (body p) ps.

Lemma procenv_safe_iden :
  procenv_safe procenv_iden.
Proof.
  red. intros p ps H1. simpls.
Qed.


(** *** Process map adequacy *)

Definition pmv_safe (env : ProcEnv)(h : Heap)(pmv : ProcMapVal) : Prop :=
  match pmv with
    | PMelem _ p P xs f =>
        forall ps : ProcStore,
          (forall x : ProcVar, In x xs -> h (f x) = Some (ps x)) ->
          proc_valid (snd (env p)) P ps
    | PMfree => True
    | PMinvalid => False
  end.

Lemma pmv_safe_eq :
  forall env h pmv1 pmv2,
  pmv_eq pmv1 pmv2 ->
  pmv_safe env h pmv1 ->
  pmv_safe env h pmv2.
Proof.
  intros env h pmv1 pmv2 H1 H2.
  unfold pmv_safe in *. destruct pmv1, pmv2; vauto.
  unfold pmv_eq in H1. destruct H1 as (F1 & F2 & F3 & F4 & F5).
  intros ps IN1. clarify. rewrite <- F3.
  apply H2. intros y IN2.
  assert (IN3 : f y = f0 y). { apply map_eq_In with xs0; vauto. }
  rewrite IN3. by apply IN1.
Qed.

Add Parametric Morphism : pmv_safe
  with signature eq ==> eq ==> pmv_eq ==> iff
    as pmv_safe_bisim_mor.
Proof.
  intros env h pmv1 pmv2 H1.
  split; intros H2.
  - apply pmv_safe_eq with pmv1; auto.
  - apply pmv_safe_eq with pmv2; auto.
Qed.

Lemma pmv_safe_iden (env : ProcEnv) :
  forall h,
  pmv_safe env h PMfree.
Proof.
  ins.
Qed.

Lemma pmv_safe_heap_acc (env : ProcEnv) :
  forall h1 h2 pmv,
    (forall l : Loc, In l (pmv_acc pmv) -> h1 l = h2 l) ->
  pmv_safe env h1 pmv ->
  pmv_safe env h2 pmv.
Proof.
  intros h1 h2 pmv H1 H2.
  unfold pmv_safe in *. desf.
  intros ps IN1. apply H2; vauto.
  intros y IN2. rewrite H1; [|by apply in_map].
  by apply IN1.
Qed.

Lemma pmv_safe_subheap (env : ProcEnv) :
  forall h1 h2 pmv,
    (forall l v, h2 l = Some v -> h1 l = Some v) ->
  pmv_safe env h1 pmv ->
  pmv_safe env h2 pmv.
Proof.
  intros h1 h2 pmv H1 H2. unfold pmv_safe in *. desf.
  intros ps IN1. apply H2. intros y IN2.
  by apply H1, IN1.
Qed.

Definition procmap_safe (env : ProcEnv)(h : Heap)(pm : ProcMap) : Prop :=
  forall pid : ProcID, pmv_safe env h (pm pid).

Lemma procmap_safe_eq :
  forall env h pm1 pm2,
  procmap_eq pm1 pm2 ->
  procmap_safe env h pm1 ->
  procmap_safe env h pm2.
Proof.
  intros env h pm1 pm2 H1 H2 pid.
  unfold procmap_safe in H2.
  specialize H2 with pid.
  unfold procmap_eq in H1.
  specialize H1 with pid.
  by rewrite <- H1.
Qed.

Add Parametric Morphism : procmap_safe
  with signature eq ==> eq ==> procmap_eq ==> iff
    as procmap_safe_bisim_mor.
Proof.
  intros env h pm1 pm2 H1. split; intros H2.
  - apply procmap_safe_eq with pm1; auto.
  - apply procmap_safe_eq with pm2; auto.
Qed.

Lemma procmap_safe_subheap (env : ProcEnv) :
  forall h1 h2 pm,
    (forall l v, h2 l = Some v -> h1 l = Some v) ->
  procmap_safe env h1 pm ->
  procmap_safe env h2 pm.
Proof.
  intros h1 h2 pm H1 H2. unfold procmap_safe in *.
  intro pid. apply pmv_safe_subheap with h1; vauto.
Qed.


(** ** Well-structured process maps *)

(** A process map [pm] is defined to be _well-structured_ if every heap location [l] is
    accessed by at most one entry of [pm]. This definition therefore implies that all
    the entries of [pm] access different heap locations (disjoint parts of the heap). *)

(** This definition is important in the soundness argument, since every heap location can
    be subject to at most one active process, and we need to make this fact explicit,
    which we do via [procmap_ws]. *)

Definition procmap_ws (pm : ProcMap) : Prop :=
  forall (pid1 pid2 : ProcID)(l : Loc),
    In l (pmv_acc (pm pid1)) ->
    In l (pmv_acc (pm pid2)) ->
    pid1 = pid2.

Lemma procmap_ws_eq :
  forall pm1 pm2,
  procmap_eq pm1 pm2 ->
  procmap_ws pm1 ->
  procmap_ws pm2.
Proof.
  intros pm1 pm2 H1 H2.
  unfold procmap_ws in *. intros pid1 pid2 l H3 H4.
  unfold procmap_eq in H1. apply H2 with l.
  - specialize H1 with pid1. by rewrite H1.
  - specialize H1 with pid2. by rewrite H1.
Qed.

Add Parametric Morphism : procmap_ws
  with signature procmap_eq ==> iff
    as procmap_ws_mor.
Proof.
  intros pm1 pm2 H1. split; intro H2.
  - apply procmap_ws_eq with pm1; auto.
  - apply procmap_ws_eq with pm2; auto.
Qed.

Lemma procmap_ws_iden :
  procmap_ws procmap_iden.
Proof.
  red. intros pid1 pid2 l H1 H2. simpls.
Qed.

Lemma procmap_ws_upd :
  forall pm pid pmv,
    (forall pid' l, pid <> pid' -> In l (pmv_acc pmv) -> In l (pmv_acc (pm pid')) -> False) ->
  procmap_ws pm ->
  procmap_ws (update pm pid pmv).
Proof.
  intros pm pid pmv H1 H2. unfold procmap_ws in *.
  intros pid1 pid2 l H3 H4.
  unfold update in H3, H4. desf.
  - apply H1 in H3; vauto.
  - apply H1 in H4; vauto.
  - by apply H2 with l.
Qed.

Lemma procmap_ws_agree :
  forall pm1 pm2,
  procmap_agree pm1 pm2 ->
  procmap_ws pm1 ->
  procmap_ws pm2.
Proof.
  intros pm1 pm2 H1 H2 pid1.
  intros pid2 l H3 H4. red in H2.
  apply H2 with l.
  - red in H1. specialize H1 with pid1. by rewrite H1.
  - red in H1. specialize H1 with pid2. by rewrite H1.
Qed.

Add Parametric Morphism : procmap_ws
  with signature procmap_agree ==> iff
    as procmap_ws_agree_mor.
Proof.
  intros pm1 pm2 H1. split; intro H2.
  - apply procmap_ws_agree with pm1; auto.
  - apply procmap_ws_agree with pm2; auto.
Qed.


(** ** Adequacy *)

(** The auxiliary predicate [invariant_sat] determines whether a resource invariant [J]
    is satisfied by the given model in the context of the given program [C]. If the 
    program is locked, we allow the resource invariant to be arbitrary (as in the proof system
    the resource invariant then becomes [Atrue]), but otherwise the model should hold w.r.t. [J]. *)

Definition invariant_sat (ph : PermHeap)(pm : ProcMap)(s g : Store)(C : GhostCmd)(J : Assn) : Prop :=
  ~ cmd_locked C -> assn_sat ph pm s g J.

Fixpoint safe (n : nat)(env : ProcEnv)(basic : Prop)(C : GhostCmd)(ph : PermHeap)(pm : ProcMap)(s g : Store)(J A : Assn) : Prop :=
  match n with
    | O => True
    | S m =>
      (* (1) terminal programs satisfy their postcondition *)
        (C = Cskip -> assn_sat ph pm s g A) /\
      (* (2) the program does not fault (which includes the absence of data-races) *)
      (forall phF pmF,
        permheap_disj ph phF ->
        procmap_disj pm pmF ->
      let h := permheap_concr (permheap_add ph phF) in
      let pm' := procmap_add pm pmF in
        heap_finite h ->
        procmap_finite pm' ->
        ~ ghost_abort h pm' s g C) /\
      (* (3) all heap accesses are in the footprint (i.e. memory safety) *)
      (forall l : Loc, cmd_acc C s l -> phc_lt PHCfree (ph l)) /\
      (* (4) all heap writes are in the footprint (i.e. memory safety) *)
      (forall l : Loc, cmd_writes C s l -> phc_full (ph l)) /\
      (* (5) after performing a computation step the program remains safe for another [m] steps *)
      (forall phJ phF pmJ pmF pmC h' s' C',
        permheap_disj ph phJ ->
        permheap_disj (permheap_add ph phJ) phF ->
        procmap_disj pm pmJ ->
        procmap_disj (procmap_add pm pmJ) pmF ->
        procmap_eq (procmap_add (procmap_add pm pmJ) pmF) pmC ->
        procmap_finite pmC ->
        procmap_ws pmC ->
        invariant_sat phJ pmJ s g C J ->
      let h := permheap_concr (permheap_add (permheap_add ph phJ) phF) in
      let hs := permheap_snapshot (permheap_add (permheap_add ph phJ) phF) in
        heap_finite h ->
        procmap_covers pmC hs ->
        procmap_safe env hs pmC ->
        prog_sos h s (plain C) h' s' C' ->
      exists ph' phJ',
        permheap_disj ph' phJ' /\
        permheap_disj (permheap_add ph' phJ') phF /\
        permheap_concr (permheap_add (permheap_add ph' phJ') phF) = h' /\
        heap_finite h' /\
        (basic -> phJ = phJ' /\ permheap_snapshot ph = permheap_snapshot ph') /\
      exists pm' pmJ' pmC',
        procmap_disj pm' pmJ' /\
        procmap_disj (procmap_add pm' pmJ') pmF /\
        procmap_eq (procmap_add (procmap_add pm' pmJ') pmF) pmC' /\
        procmap_finite pmC' /\
        procmap_ws pmC' /\
        (basic -> procmap_eq pm pm' /\ procmap_eq pmJ pmJ') /\
      let hs' := permheap_snapshot (permheap_add (permheap_add ph' phJ') phF) in
        procmap_covers pmC' hs' /\
        procmap_safe env hs' pmC' /\
      exists g' C'',
        plain C'' = C' /\
        ghost_sos h pmC s g C h' pmC' s' g' C'' /\
        invariant_sat phJ' pmJ' s' g' C'' J /\
        safe m env basic C'' ph' pm' s' g' J A)
  end.

Lemma safe_procmap_eq (env : ProcEnv) :
  forall n basic C ph pm1 pm2 s g J A,
  procmap_eq pm1 pm2 ->
  safe n env basic C ph pm1 s g J A ->
  safe n env basic C ph pm2 s g J A.
Proof.
  intros [|n] basic C ph pm1 pm2 s g J A EQ SAFE. vauto.
  destruct SAFE as (TERM & ABORT & ACC & WRITE & SAFE).
  repeat split; vauto.
  (* (1) terminal programs *)
  - intro H. rewrite <- EQ.
    by apply TERM.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT1.
    rewrite <- EQ in ABORT1.
    apply ABORT in ABORT1; vauto; by rewrite EQ.
  (* (5) program step *)
  - simpl.
    intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS INV FIN2 COV1 PSAFE STEP.
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto; try by rewrite EQ.
    destruct STEP as (ph' & phJ' & D5 & D6 & H2 & FIN3 & BASIC1 & STEP).
    destruct STEP as (pm' & pmJ' & pmC' & D7 & D8 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE1 & STEP).
    destruct STEP as (g' & C'' & H4 & GSTEP & INV1 & SAFE1). clarify.
    exists ph', phJ'. intuition vauto.
    exists pm', pmJ', pmC'. intuition vauto.
    by rewrite <- EQ.
Qed.

Lemma safe_assn_equiv_inv (env : ProcEnv) :
  forall n basic C ph pm s g R1 R2 A,
  assn_equiv R1 R2 ->
  safe n env basic C ph pm s g R1 A ->
  safe n env basic C ph pm s g R2 A.
Proof.
  induction n as [|n IH]. vauto.
  intros basic C ph pm s g R1 R2 A (AEQ1&AEQ2) SAFE. vauto.
  destruct SAFE as (TERM & ABORT & ACC & WRITE & SAFE).
  repeat split; vauto. simpl.
  intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H2 FIN1 WS INV FIN2 COV1 PSAFE STEP.
  apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto.
  - destruct STEP as (ph' & phJ' & D5 & D6 & H3 & FIN3 & BASIC1 & STEP).
    destruct STEP as (pm' & pmJ' & pmC' & D7 & D8 & H4 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE1 & STEP).
    destruct STEP as (g' & C'' & H5 & GSTEP & INV1 & SAFE1). clarify.
    exists ph', phJ'. intuition vauto.
    exists pm', pmJ', pmC'. intuition vauto.
    exists g',C''. intuition vauto.
    + red. ins. apply AEQ1; auto.
      * by apply permheap_disj_valid_r in D5.
      * by apply procmap_disj_valid_r in D7.
    + by apply IH with R1.
  - red. ins. apply AEQ2; auto.
    + by apply permheap_disj_valid_r in D1.
    + by apply procmap_disj_valid_r in D3.
Qed.

Lemma safe_assn_equiv_post (env : ProcEnv) :
  forall n basic C ph pm s g R A1 A2,
  permheap_valid ph ->
  procmap_valid pm ->
  assn_equiv A1 A2 ->
  safe n env basic C ph pm s g R A1 ->
  safe n env basic C ph pm s g R A2.
Proof.
  induction n as [|n IH]. vauto.
  intros basic C ph pm s g R A1 A2 V1 V2 (AEQ1&AEQ2) SAFE. vauto.
  destruct SAFE as (TERM & ABORT & ACC & WRITE & SAFE).
  repeat split; vauto.
  - ins. apply AEQ1; auto.
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H2 FIN1 WS INV FIN2 COV1 PSAFE STEP.
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto.
    destruct STEP as (ph' & phJ' & D5 & D6 & H3 & FIN3 & BASIC1 & STEP).
    destruct STEP as (pm' & pmJ' & pmC' & D7 & D8 & H4 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE1 & STEP).
    destruct STEP as (g' & C'' & H5 & GSTEP & INV1 & SAFE1). clarify.
    exists ph', phJ'. intuition vauto.
    exists pm', pmJ', pmC'. intuition vauto.
    exists g',C''. intuition vauto.
    apply IH with A1; auto.
    + by apply permheap_disj_valid_l in D5.
    + by apply procmap_disj_valid_l in D7.
    + split; auto.
Qed.

Add Parametric Morphism : safe
  with signature eq ==> eq ==> eq ==> eq ==> eq ==> procmap_eq ==> eq ==> eq ==> assn_equiv ==> eq ==> iff
    as safe_bisim_mor.
Proof.
  intros n env basic C ph pm1 pm2 H1 s g R1 R2 (H2&H3) A.
  split; intro H4.
  - apply safe_procmap_eq with pm1; auto.
    by apply safe_assn_equiv_inv with R1.
  - apply safe_procmap_eq with pm2; auto.
    by apply safe_assn_equiv_inv with R2.
Qed.

Open Scope nat_scope.

Lemma safe_mono (env : ProcEnv) :
  forall m n basic C ph pm s g J A,
  m <= n ->
  safe n env basic C ph pm s g J A ->
  safe m env basic C ph pm s g J A.
Proof.
  induction m as [|m IH]; intros n basic C ph pm a g J A LE SAFE.
  vauto. repeat split.
  (* (1) terminating programs *)
  - intro H. clarify. destruct n.
    by apply Nat.nle_succ_0 in LE.
    simpls. intuition.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    destruct n. by apply Nat.nle_succ_0 in LE.
    destruct SAFE as (_ & ABORT1 & _).
    by apply ABORT1 with phF pmF.
  (* (3) heap accesses are in footprint *)
  - intros l H1.
    destruct n. by apply Nat.nle_succ_0 in LE.
    destruct SAFE as (_ & _ & LOC & _).
    by apply LOC in H1.
  (* (4) heap writes are in footprint *)
  - intros l H1.
    destruct n. by apply Nat.nle_succ_0 in LE.
    destruct SAFE as (_ & _ & _ & WRITES & _).
    by apply WRITES in H1.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE STEP.
    destruct n. by apply Nat.nle_succ_0 in LE.
    destruct SAFE as (TERM & ABORT' & LOCr & LOCw & SAFE).
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto.
    destruct STEP as (ph' & phJ' & D5 & D6 & H2 & FIN3 & BASIC1 & STEP).
    destruct STEP as (pm' & pmJ' & pmC' & D7 & D8 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE1 & STEP).
    destruct STEP as (g' & C'' & H4 & GSTEP & INV1 & SAFE1). clarify.
    exists ph', phJ'. intuition.
    exists pm', pmJ', pmC'. intuition.
    exists g', C''. intuition.
    apply IH with n; auto.
    by apply le_S_n.
Qed.

Close Scope nat_scope.

Lemma safe_skip (env : ProcEnv) :
  forall n basic ph pm s g J A,
  safe (S n) env basic Cskip ph pm s g J A ->
  assn_sat ph pm s g A.
Proof.
  intros n basic ph pm s g J A H.
  simpls. des. by apply H.
Qed.

Lemma safe_done (env : ProcEnv) :
  forall n basic ph pm s g J A,
  assn_sat ph pm s g A ->
  safe n env basic Cskip ph pm s g J A.
Proof.
  intros [|n] basic ph pm s g J A H. vauto.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS INV FIN2 COV1 PSAFE STEP.
    inv STEP.
Qed.

Lemma safe_agree (env : ProcEnv) :
  forall n basic C ph pm s1 s2 g J A,
    (forall x, assn_fv A x -> s1 x = s2 x) ->
    (forall x, assn_fv J x -> s1 x = s2 x) ->
    (forall x, cmd_fv C x -> s1 x = s2 x) ->
  safe n env basic C ph pm s1 g J A ->
  safe n env basic C ph pm s2 g J A.
Proof.
  induction n as [|n IH]; auto.
  intros basic C ph pm s1 s2 g J A F1 F2 F3 SAFE.
  repeat split.
  (* (1) terminal programs *)
  - intro H. destruct SAFE as (TERM & _).
    rewrite <- assn_sat_agree with (s1 := s1); auto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT1.
    apply ghost_abort_agree with (s2 := s1) in ABORT1; auto.
    destruct SAFE as (_ & ABORT & _).
    apply ABORT with phF pmF; auto.
    intros x H1. symmetry. by apply F3.
  (* (3) heap reads are in footprint *)
  - intros l S1. destruct SAFE as (_ & _ & LOC & _).
    rewrite <- cmd_acc_agree with (s3 := s1) in S1; auto.
  (* (4) heap writes are in footprint *)
  - intros l S1. destruct SAFE as (_ & _ & _ & WRITES & _).
    rewrite <- cmd_writes_agree with (s3 := s1) in S1; auto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s2' C' D1 D2 D3 D4 H1 FIN1 WS1 SAT FIN2 COV1 PSAFE1 STEP.
    generalize STEP. intro STEP'.
    apply prog_sos_agree with (s2 := s1)(phi := fun x => cmd_fv C x \/ assn_fv J x \/ assn_fv A x) in STEP.
    destruct STEP as (s1' & H2  & STEP).
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; intuition vauto. clear SAFE.
    destruct STEP as (ph' & phJ' & D5 & D6 & H3 & FIN3 & BASIC1 & STEP).
    destruct STEP as (pm' & pmJ' & pmC' & D7 & D8 & H4 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE2 & STEP).
    destruct STEP as (g' & C'' & H5 & GSTEP & INV1 & SAFE1). clarify.
    exists ph', phJ'. intuition.
    exists pm', pmJ', pmC'. intuition.
    exists g', C''. intuition vauto.
    { (* ghost semantics can make a matching step *)
    apply ghost_sos_agree_sim with s1 s1'; vauto.
    + intros x H3. symmetry. by apply F3.
    + intros x H3. apply H2. by left. }
    { (* the resource invariant still holds after the program step *)
    red. unfold invariant_sat in INV1.
    intro H. apply assn_sat_agree with (s1 := s1').
    + intros x F4. symmetry. apply H2. right. by left.
    + by apply INV1. }
    { (* program is safe for [n] more steps *)
    apply IH with s1'; auto.
    + intros x H. symmetry. apply H2. by repeat right.
    + intros x H. symmetry. apply H2. right. by left.
    + intros x H3. symmetry. apply H2. left.
      apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (G1 & _). by apply G1. }
    { (* resource invariant holds before program step *)
    red. unfold invariant_sat in SAT.
    intros H'. apply assn_sat_agree with (s1 := s2).
    + intros x F4. symmetry. by apply F2.
    + by apply SAT. }
    { (* all free variables of [C] are contained *)
    intros x H. left. by rewrite cmd_fv_plain. }
    { (* program stores agree on all free variables *)
    intros x [F | [F | F]]; symmetry.
    by apply F3. by apply F2. by apply F1. }
Qed.

Lemma safe_agree_ghost (env : ProcEnv) :
  forall n basic C ph pm s g1 g2 J A,
    (forall x, assn_fv A x -> g1 x = g2 x) ->
    (forall x, assn_fv J x -> g1 x = g2 x) ->
    (forall x, cmd_fv C x -> g1 x = g2 x) ->
  safe n env basic C ph pm s g1 J A ->
  safe n env basic C ph pm s g2 J A.
Proof.
  induction n; vauto.
  intros basic C ph pm s g1 g2 J A FV1 FV2 FV3 SAFE.
  repeat split.
  (* (1) terminal programs *)
  - intro H. destruct SAFE as (TERM & _).
    rewrite <- assn_sat_ghost_agree with (g1 := g1); auto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT'.
    apply ghost_abort_agree_g with (g2 := g1) in ABORT'; auto.
    destruct SAFE as (_ & ABORT & _).
    apply ABORT with phF pmF; auto.
    unfold store_agree in *.
    intros x FV4. symmetry. by apply FV3.
  (* (3) all heap reads are in the footprint *)
  - destruct SAFE as (_ & _ & ACC & _). vauto.
  (* (4) heap writes are in the footprint *)
  - destruct SAFE as (_ & _ & _ & WRITES & _). vauto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; auto.
    destruct STEP as (ph' & phJ' & D5 & D6 & H2 & FIN3 & BASIC1 & STEP).
    destruct STEP as (pm' & pmJ' & pmC' & D7 & D8 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE & STEP).
    destruct STEP as (g' & C'' & H4 & GSTEP & INV1 & SAFE1). clarify.
    exists ph', phJ'. intuition.
    exists pm', pmJ', pmC'. intuition.
    apply ghost_sos_agree_g with (g2 := g2)(phi := fun x => cmd_fv C x \/ assn_fv J x \/ assn_fv A x) in GSTEP; auto.
    destruct GSTEP as (g2' & F4 & GSTEP).
    exists g2', C''. intuition vauto.
    { (* resource invariant still holds after program step *)
    red. unfold invariant_sat in INV1.
    intro H4. apply assn_sat_ghost_agree with g'.
    + intros x F5. symmetry. apply F4. right. by left.
    + by apply INV1. }
    { (* program is safe for [n] more steps *)
    apply IHn with g'; auto.
    apply ghost_sos_fv_mod in GSTEP.
    destruct GSTEP as (F5 & F6 & F7 & F8).
    intros x F9. apply F5 in F9.
    apply F4. by left. }
    { (* The ghost stores [g1] and [g2] agree on all free variables in [C], [J], and [A] *)
    intros x [F5 | [F5 | F5]].
    by apply FV3. by apply FV2. by apply FV1. }
    { (* resource invariant holds before program step *)
    red. unfold invariant_sat in INV.
    intros H'. apply assn_sat_ghost_agree with g2.
    + intros x F4. by apply FV2.
    + by apply INV. }
Qed.

Lemma safe_disj_weaken (env : ProcEnv) :
  forall n basic C ph pm s g R A1 A2,
  safe n env basic C ph pm s g R A1 ->
  safe n env basic C ph pm s g R (Adisj A1 A2).
Proof.
  induction n as [|n IH]. vauto.
  intros basic C ph pm s g R A1 A2 SAFE.
  destruct SAFE as (TERM & ABORT & ACC & WRITE & SAFE).
  repeat split; vauto.
  - ins. left. by apply TERM.
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H2 FIN1 WS INV FIN2 COV1 PSAFE STEP.
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; vauto.
    destruct STEP as (ph' & phJ' & D5 & D6 & H3 & FIN3 & BASIC1 & STEP).
    destruct STEP as (pm' & pmJ' & pmC' & D7 & D8 & H4 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE1 & STEP).
    destruct STEP as (g' & C'' & H5 & GSTEP & INV1 & SAFE1). clarify.
    exists ph', phJ'. intuition vauto.
    exists pm', pmJ', pmC'. intuition vauto.
    exists g',C''. intuition vauto. by apply IH.
Qed.


(** ** Soundness of the proof rules *)

(** The meaning of Hoare triples is given by [csl]. *)

Definition csl (env : ProcEnv)(basic : Prop)(J : Assn)(A1 : Assn)(C : GhostCmd)(A2 : Assn) : Prop :=
  (* (1) the program [C] is a _user program_*)
  cmd_user C /\
  (* (2) the program [C] is _safe_ for any number of steps, provided that [C] is a well-formed program and [env] is a safe environment. *)
  (procenv_safe env ->
  forall n ph pm s g,
    permheap_valid ph ->
    procmap_valid pm ->
    cmd_wf C ->
    assn_sat ph pm s g A1 ->
    safe n env basic C ph pm s g J A2).

Add Parametric Morphism : csl
  with signature eq ==> eq ==> assn_equiv ==> assn_equiv ==> eq ==> assn_equiv ==> iff
    as csl_mor.
Proof.
  intros env basic R1 R2 H1 A1 A2 H2 C A3 A4 H3.
  split; intros (H4&H5).
  - red. split; vauto. intros SAFE n ph pm s g V1 V2 WF1 SAT1.
    rewrite <- H1. apply safe_assn_equiv_post with A3; auto.
    apply H5; vauto. destruct H2 as (_&H2). by apply H2.
  - red. split; vauto. intros SAFE n ph pm s g V1 V2 WF1 SAT1.
    rewrite H1. apply safe_assn_equiv_post with A4; auto.
    + by symmetry.
    + apply H5; vauto. destruct H2 as (H2&_). by apply H2.
Qed.

Lemma csl_trivial (env : ProcEnv) :
  forall basic J C A,
  cmd_user C ->
  csl env basic J (Aplain (Bconst false)) C A.
Proof.
  intros basic J C A USER. red. split; vauto.
Qed.


(** *** Skip rule *)

Theorem rule_skip (env : ProcEnv) :
  forall basic J A,
  csl env basic J A Cskip A.
Proof.
  intros basic J A. red. split. vauto.
  intros ESAFE n ph pm s g V1 V2 WF SAT.
  by apply safe_done.
Qed.


(** *** Sequential composition *)

Open Scope nat_scope.

Lemma safe_seq (env : ProcEnv) :
  forall n basic C1 C2 J A1 A2 ph pm s g,
  permheap_valid ph ->
  procmap_valid pm ->
  safe n env basic C1 ph pm s g J A1 ->
  (forall m ph' pm' s' g',
    m <= n ->
    permheap_valid ph' ->
    procmap_valid pm' ->
    assn_sat ph' pm' s' g' A1 ->
    safe m env basic C2 ph' pm' s' g' J A2) ->
  safe n env basic (Cseq C1 C2) ph pm s g J A2.
Proof.
  induction n as [|n IH]; vauto.
  intros basic C1 C2 J A1 A2 ph pm s g V1 V2 SAFE1 SAFE2.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    destruct SAFE1 as (_ & ABORT2 & _).
    inv ABORT. by apply ABORT2 in H4.
  (* (3) all heap accesses are in footprint *)
  - simpls. intuition vauto.
  (* (4) all heap writes are in footprint *)
  - simpls. intuition vauto.
  (* (5) program step *)
  - destruct SAFE1 as (TERM & ABORT & ACC & WRITE & SAFE1). simpl.
    intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP; clear STEP.
    (* left program [C1] is empty *)
    + rename s' into s.
      symmetry in H3.
      apply plain_skip in H3. clarify.
      exists ph, phJ. intuition.
      exists pm, pmJ, pmC. intuition.
      exists g, C2. intuition auto; vauto.
      unfold invariant_sat in INV. intuition. red. done.
    (* left program [C1] is not empty *)
    + apply SAFE1 with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in H7; auto.
      destruct H7 as (ph' & phJ' & D5 & D6 & H2 & FIN3 & BASIC1 & H7).
      destruct H7 as (pm' & pmJ' & pmC' & D7 & D8 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE & H7).
      destruct H7 as (g' & C'' & H4 & GSTEP & INV1 & SAFE3). clarify.
      exists ph', phJ'. intuition.
      exists pm', pmJ', pmC'. intuition.
      exists g', (Cseq C'' C2). intuition vauto.
      apply IH with A1; auto.
      * by apply permheap_disj_valid_l in D5.
      * by apply procmap_disj_valid_l in D7.
Qed.

Close Scope nat_scope.

Theorem rule_seq (env : ProcEnv) :
  forall basic J A1 A2 A3 C1 C2,
  csl env basic J A1 C1 A2 ->
  csl env basic J A2 C2 A3 ->
  csl env basic J A1 (Cseq C1 C2) A3.
Proof.
  intros basic J A1 A2 A3 C1 C2 CSL1 CSL2.
  red. split; vauto.
  (* the program [C1; C2] is a _user program_ *)
  - constructor.
    + by destruct CSL1 as (? & _).
    + by destruct CSL2 as (? & _).
  (* the program [C1; C2] is safe for any number of steps *)
  - intros ENV n ph pm s g V1 V2 WF SAT.
    apply safe_seq with A2; auto.
    (* [C1] is safe for any number of steps *)
    + destruct CSL1 as (_ & SAFE1).
      apply SAFE1; auto. inv WF.
    (* [C2] is safe for any number of steps *)
    + destruct CSL2 as (_ & SAFE2).
      intros m ph' pm' s' g' LE V3 V4 SAT'.
      apply SAFE2; auto. inv WF.
Qed.


(** *** If-then-else rule *)

Lemma safe_ite (env : ProcEnv) :
  forall n basic J A1 A2 B C1 C2 ph pm s g,
  assn_sat ph pm s g A1 ->
    (assn_sat ph pm s g (Astar A1 (Aplain B)) -> safe n env basic C1 ph pm s g J A2) ->
    (assn_sat ph pm s g (Astar A1 (Aplain (Bnot B))) -> safe n env basic C2 ph pm s g J A2) ->
  safe n env basic (Cite B C1 C2) ph pm s g J A2.
Proof.
  induction n as [|n IH]; vauto.
  intros basic J A1 A2 B C1 C2 ph pm s g SAT1 SAFE1 SAFE2.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP; clear STEP.
    (* computation step in [C1] *)
    + rename s' into s.
      exists ph, phJ. intuition.
      exists pm, pmJ, pmC. intuition.
      exists g, C1. intuition vauto.
      (* the resource invariant is still maintained after the step *)
      * unfold invariant_sat. intro H. by apply INV.
      (* the program is safe for [n] more steps *)
      * apply safe_mono with (S n); auto.
        apply SAFE1. simpl.
        exists ph, permheap_iden. repeat split; vauto.

        { (* [ph] is disjoint with the identity heap *)
        apply permheap_disj_iden_l.
        by apply permheap_disj_valid_l in D1. }
        { (* [ph + iden] equals [ph] *)
        by rewrite permheap_add_iden_l. }

        exists pm, procmap_iden. repeat split; vauto.

        { (* [pm] is disjoint with the identity heap *)
        apply procmap_disj_iden_l.
        by apply procmap_disj_valid_l in D3. }
        { (* [pm + iden] equals [pm] *)
        by rewrite procmap_add_iden_l. }

    (* computation step in [C2] *)
    + rename s' into s.
      exists ph, phJ. intuition.
      exists pm, pmJ, pmC. intuition.
      exists g, C2. intuition vauto.
      (* the resource invariant is still maintained after the step *)
      * unfold invariant_sat.
        intro H. by apply INV.
      (* the program is safe for [n] more steps *)
      * apply safe_mono with (S n). auto.
        apply SAFE2. simpl.
        exists ph, permheap_iden. repeat split; auto.

        { (* [ph] is disjoint with the identity heap *)
        apply permheap_disj_iden_l.
        by apply permheap_disj_valid_l in D1. }
        { (* [ph + iden] equals [ph] *)
        by rewrite permheap_add_iden_l. }

        exists pm, procmap_iden. repeat split; vauto.

        { (* [pm] is disjoint with the identity heap *)
        apply procmap_disj_iden_l.
        by apply procmap_disj_valid_l in D3. }
        { (* [pm + iden] equals [pm] *)
        by rewrite procmap_add_iden_l. }
Qed.

Theorem rule_ite (env : ProcEnv) :
  forall basic J A1 A2 B C1 C2,
  csl env basic J (Astar A1 (Aplain B)) C1 A2 ->
  csl env basic J (Astar A1 (Aplain (Bnot B))) C2 A2 ->
  csl env basic J A1 (Cite B C1 C2) A2.
Proof.
  intros basic J A1 A2 B C1 C2 CSL1 CSL2. red. split.
  (* the program [Cite B C1 C2] is a user program *)
  - constructor.
    + by destruct CSL1 as (? & _).
    + by destruct CSL2 as (? & _).
  (* the program [Cite B C1 C2] is safe for any number of steps *)
  - intros ENV n ph pm s g V1 V2 WF SAT.
    apply safe_ite with A1; auto.
    (* [C1] is safe for any number of steps *)
    + intro SAT'. destruct CSL1 as (_ & SAFE1).
      apply SAFE1; auto. inv WF.
    (* [C2] is safe for any number of steps *)
    + intro SAT'. destruct CSL2 as (_ & SAFE2).
      apply SAFE2; auto. inv WF.
Qed.


(** *** While rule *)

Lemma safe_while (env : ProcEnv) :
  forall n basic B C ph pm s g J A,
  csl env basic J (Astar A (Aplain B)) C A ->
  assn_sat ph pm s g A ->
  cmd_wf C ->
  procenv_safe env ->
  safe n env basic (Cwhile B C) ph pm s g J (Astar A (Aplain (Bnot B))).
Proof.
  induction n as [|n IH]; vauto.
  intros basic B C ph pm s g J A CSL SAT1 WF ENV.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT. inv ABORT.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE STEP.
    inv STEP. clear STEP.
    exists ph, phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, (Cite B (Cseq C (Cwhile B C)) Cskip).
    intuition vauto. rename s' into s.
    apply safe_ite with A; vauto.
    (* [C; while B C] is safe for [n] computation steps *)
    + intro SAT2. apply safe_seq with A; auto.
      { (* [ph] is valid *)
      by apply permheap_disj_valid_l in D1. }
      { (* [pm] is valid *)
      by apply procmap_disj_valid_l in D3. }
      { (* the program [C] is safe for [n] more steps *)
      apply CSL; auto.
      - by apply permheap_disj_valid_l in D1.
      - by apply procmap_disj_valid_l in D3. }
      { (* the composite program [Cwhile B C] is safe *)
      intros m ph' pm' s' g' LE V1 V2 SAT3.
      apply safe_mono with n; auto. }
    (* the postcondition holds in case [C] is empty *)
    + by apply safe_done.
Qed.

Theorem rule_while (env : ProcEnv) :
  forall basic J A B C,
  csl env basic J (Astar A (Aplain B)) C A ->
  csl env basic J A (Cwhile B C) (Astar A (Aplain (Bnot B))).
Proof.
  intros basic J A B C CSL. red. split.
  (* the program [Cwhile B C] is a _user program_ *)
  - by destruct CSL as (? & _).
  (* the program [Cwhile B C] is safe for any number of steps *)
  - intros. by apply safe_while.
Qed.


(** *** Assign rule *)

Lemma safe_assign (env : ProcEnv) :
  forall n basic J A x E ph pm s g,
  ~ assn_fv J x ->
  assn_sat ph pm s g (assn_subst x E A) ->
  safe n env basic (Cass x E) ph pm s g J A.
Proof.
  induction n as [|n IH]; vauto.
  intros basic J A x E ph pm s g H1 H2.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H3 FIN1 WS1 INV FIN2 COV1 PSAFE STEP.
    inv STEP. clear STEP.
    exists ph, phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, Cskip. intuition vauto.
    (* the resource invariant [J] is still satisfied *)
    + unfold invariant_sat in INV.
      red. intros _. rewrite assn_sat_upd; auto.
    (* program remains safe for [n] more steps *)
    + apply safe_done.
      by rewrite assn_sat_subst in H2.
Qed.

Theorem rule_assign (env : ProcEnv) :
  forall basic J A x E,
  ~ assn_fv J x ->
  csl env basic J (assn_subst x E A) (Cass x E) A.
Proof.
  ins. red. split; vauto. ins. by apply safe_assign.
Qed.


(** *** Rule of consequence *)

Lemma safe_conseq (env : ProcEnv) :
  forall n basic C ph pm s g J A1 A2,
  permheap_valid ph ->
  procmap_valid pm ->
  assn_entails A1 A2 ->
  safe n env basic C ph pm s g J A1 ->
  safe n env basic C ph pm s g J A2.
Proof.
  induction n as [|n IH]; vauto.
  intros basic C ph pm s g J A1 A2 V1 V2 ENT SAFE.
  repeat split; vauto.
  (* (1) terminal programs *)
  - intros ?. clarify.
    apply safe_skip in SAFE.
    by apply ENT.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    destruct SAFE as (_ & ABORT2 & _).
    by apply ABORT2 in ABORT.
  (* (3) all heap accesses are in footprint *)
  - intros l H.
    destruct SAFE as (_ & _ & ACC & _).
    apply ACC in H. vauto.
  (* (4) all heap writes are in footprint *)
  - intros l H.
    destruct SAFE as (_ & _ & _ & WRITE & _).
    apply WRITE in H. vauto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H3 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    destruct SAFE as (TERM & ABORT & ACC & WRITE & SAFE).
    apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in STEP; auto.
    destruct STEP as (ph' & phJ' & D5 & D6 & H2 & FIN3 & BASIC1 & STEP).
    destruct STEP as (pm' & pmJ' & pmC' & D7 & D8 & H4 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE2 & STEP).
    destruct STEP as (g' & C'' & H5 & GSTEP & INV1 & SAFE1). clarify.
    exists ph', phJ'. intuition.
    exists pm', pmJ', pmC'. intuition.
    exists g', C''. intuition.
    apply IH with A1; auto.
    (* [ph'] is valid *)
    + by apply permheap_disj_valid_l in D5.
    (* [pm'] is valid *)
    + by apply procmap_disj_valid_l in D7.
Qed.

Theorem rule_conseq (env : ProcEnv) :
  forall basic J A1 A2 A1' A2' C,
  assn_entails A1 A1' ->
  assn_entails A2' A2 ->
  csl env basic J A1' C A2' ->
  csl env basic J A1 C A2.
Proof.
  intros basic J A1 A2 A1' A2' C EQ1 EQ2 CSL. red. split.
  (* the program [C] is a _user program_ *)
  - by destruct CSL as (? & _).
  (* the program [C] is safe for any number of steps *)
  - intros ENV n ph pm s g V1 V2 WF SAT.
    apply safe_conseq with A2'; vauto.
    destruct CSL as (_ & SAFE).
    apply SAFE; auto.
Qed.


(** *** Disjunction rule *)

Theorem rule_disj (env : ProcEnv) :
  forall basic J A1 A2 A1' A2' C,
  csl env basic J A1 C A1' ->
  csl env basic J A2 C A2' ->
  csl env basic J (Adisj A1 A2) C (Adisj A1' A2').
Proof.
  intros basic J A1 A2 A1' A2' C CSL1 CSL2. red. split.
  (* [C] is a basic program *)
  - red in CSL1. by destruct CSL1 as (? & _).
  (* [C] is safe for any number of steps *)
  - intros ENV n ph pm s g V1 V2 WF SAT.
    destruct CSL1 as (_ & CSL1).
    destruct CSL2 as (_ & CSL2).
    simpl in SAT. destruct SAT as [SAT | SAT].
    + apply safe_conseq with A1'; vauto. by apply CSL1.
    + apply safe_conseq with A2'; vauto. by apply CSL2.
Qed.

Corollary rule_disj_l (env : ProcEnv) :
  forall basic J A1 A2 A3 C,
  csl env basic J A2 C A1 ->
  csl env basic J A3 C A1 ->
  csl env basic J (Adisj A2 A3) C A1.
Proof.
  intros basic J A1 A2 A3 C H1 H2.
  apply rule_conseq with (A1' := Adisj A2 A3)(A2' := Adisj A1 A1); auto.
  - by apply assn_disj_idemp.
  - by apply rule_disj.
Qed.

Corollary rule_disj_r (env : ProcEnv) :
  forall basic J A1 A2 A3 C,
  csl env basic J A1 C A2 ->
  csl env basic J A1 C A3 ->
  csl env basic J A1 C (Adisj A2 A3).
Proof.
  intros basic J A1 A2 A3 C H1 H2.
  apply rule_conseq with (A1' := Adisj A1 A1)(A2' := Adisj A2 A3); auto.
  - by apply assn_disj_idemp.
  - by apply rule_disj.
Qed.

Lemma rule_disj_weaken (env : ProcEnv) :
  forall basic J A1 A2 A3 C,
  csl env basic J A1 C A2 ->
  csl env basic J A1 C (Adisj A2 A3).
Proof.
  intros basic J A1 A2 A3 C (H1&H2).
  red. split; auto. ins. apply safe_disj_weaken; auto.
Qed.


(** *** Frame rule *)

(** The proof itself is not particularly difficult, but requires a lot of algebraic puzzling
    to ensure that e.g. certain additions and compositions of heaps and process maps are still disjoint. *)

Lemma safe_frame (env : ProcEnv) :
  forall n basic C ph1 ph2 pm1 pm2 s g J A1 A2,
  permheap_disj ph1 ph2 ->
  procmap_disj pm1 pm2 ->
  disjoint (assn_fv A2) (cmd_mod C) ->
  assn_sat ph2 pm2 s g A2 ->
  safe n env basic C ph1 pm1 s g J A1 ->
  safe n env basic C (permheap_add ph1 ph2) (procmap_add pm1 pm2) s g J (Astar A1 A2).
Proof.
  induction n as [|n IH]; vauto.
  intros basic C ph1 ph2 pm1 pm2 s g J A1 A2 D1 D2 FV1 SAT1 SAFE1.
  repeat split; vauto.
  (* (1) terminal programs *)
  - intros ?. clarify.
    destruct SAFE1 as (TERM & _).
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT1.
    destruct SAFE1 as (_ & ABORT2 & _).
    rewrite permheap_add_assoc in ABORT1.
    rewrite procmap_add_assoc in ABORT1.
    apply ABORT2 in ABORT1; vauto.
    (* [ph1] is disjoint with [ph2 + phF] *)
    + by apply permheap_disj_assoc_l.
    (* [pm1] is disjoint with [pm2 + pmF] *)
    + by apply procmap_disj_assoc_l.
    (* the combined heap [ph1 + ph2 + phF] is finite *)
    + by rewrite <- permheap_add_assoc.
    (* the combined process map [pm1 + pm2 + pmF] is finite *)
    + by rewrite <- procmap_add_assoc.
  (* (3) all heap accesses are in the footprint *)
  - intros l FV2. destruct SAFE1 as (_ & _ & ACC & _).
    rewrite <- permheap_add_cell.
    apply phc_lt_weaken; auto.
  (* (4) all heap writes are in the footprint *)
  - intros l FV2. destruct SAFE1 as (_ & _ & _ & WRITES & _).
    rewrite <- permheap_add_cell.
    apply phc_full_add; auto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    destruct SAFE1 as (_ & _ & _ & _ & SAFE1).
    rewrite permheap_add_swap_r with (ph2 := ph2) in STEP.
    rewrite permheap_add_swap_r with (ph2 := ph2) in STEP.
    rewrite permheap_add_assoc in STEP.
    rewrite permheap_add_comm with phF ph2 in STEP.
    apply SAFE1 with (pmJ := pmJ)(pmF := procmap_add pm2 pmF)(pmC := pmC) in STEP; clear SAFE1; auto.
    destruct STEP as (ph' & phJ' & D7 & D8 & H2 & FIN3 & BASIC1 & STEP).
    destruct STEP as (pm' & pmJ' & pmC' & D9 & D10 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE2 & STEP).
    destruct STEP as (g' & C'' & H4 & GSTEP & INV1 & SAFE1). clarify.
    exists (permheap_add ph' ph2), phJ'. intuition.
    { (* disjointness of [ph' + ph2] and [phJ'] *)
    apply permheap_disj_add_r in D8; auto.
    + rewrite permheap_add_comm in D8.
      apply permheap_disj_assoc_l in D8; auto.
    + apply permheap_disj_add_l with ph1; auto.
      apply permheap_disj_add_l with phJ; auto.
      by rewrite permheap_add_comm. }
    { (* disjointness of [ph' + ph2 + phJ'] and [phF] *)
    rewrite permheap_add_swap_r.
    apply permheap_disj_assoc_r; auto.
    apply permheap_disj_add_l with ph1; auto.
    apply permheap_disj_add_l with phJ; auto.
    by rewrite permheap_add_comm. }
    { (* heap concretisation is proper *)
    rewrite permheap_add_swap_r with (ph2 := ph2).
    by rewrite permheap_add_assoc. }
    { (* snapshot values are preserved, given that [C] is basic *)
    apply permheap_snapshot_disj_add_l; auto.
    apply permheap_disj_add_l with phJ; auto.
    - rewrite H2. by symmetry.
    - apply permheap_disj_add_r with phF; auto.
      + apply permheap_disj_add_l with ph1; auto.
        apply permheap_disj_add_l with phJ; auto.
        by rewrite permheap_add_comm.
      + rewrite permheap_add_comm with phJ ph'. by rewrite H2. }
    exists (procmap_add pm' pm2), pmJ', pmC'. intuition.
    { (* disjointness of [pm' + pm2] and [pmJ'] *)
    apply procmap_disj_add_r in D10; auto.
    + rewrite procmap_add_comm in D10.
      apply procmap_disj_assoc_l in D10; auto.
    + apply procmap_disj_add_l with pm1; auto.
      apply procmap_disj_add_l with pmJ; auto.
      by rewrite procmap_add_comm. }
    { (* disjointness of [pm' + pm2 + pmJ'] and [pmF] *)
    rewrite procmap_add_swap_r.
    apply procmap_disj_assoc_r; auto.
    apply procmap_disj_add_l with pm1; auto.
    apply procmap_disj_add_l with pmJ; auto.
    by rewrite procmap_add_comm. }
    { (* structure of [pmC] is proper *)
    rewrite <- H3.
    by rewrite procmap_add_swap_r with (pm2 := pm2). }
    { (* the process map has not been changed if [C] is basic *)
    by rewrite H5. }
    { (* [pmC'] covers the new snapshot heap *)
    rewrite permheap_add_swap_r with (ph2 := ph2).
    by rewrite permheap_add_assoc. }
    { (* the process map [pmC] is safe wrt. [ph + ph2 + phJ' + phF] *)
    rewrite permheap_add_swap_r with (ph2 := ph2).
    by rewrite permheap_add_assoc. }
    exists g', C''. intuition.
    { (* the ghost semantics can make a matching step *)
    rewrite permheap_add_swap_r with (ph2 := ph2).
    by rewrite permheap_add_assoc. }
    apply IH; vauto.
    { (* disjointness of [ph'] and [phF] *)
    apply permheap_disj_add_l with phJ'; auto.
    rewrite permheap_add_comm.
    apply permheap_disj_add_r with phF; auto.
    apply permheap_disj_add_l with ph1; auto.
    apply permheap_disj_add_l with phJ; auto.
    by rewrite permheap_add_comm. }
    { (* disjointness of [pm'] and [pm2] *)
    apply procmap_disj_add_l with pmJ'; auto.
    rewrite procmap_add_comm.
    apply procmap_disj_add_r with pmF; auto.
    apply procmap_disj_add_l with pm1; auto.
    apply procmap_disj_add_l with pmJ; auto.
    by rewrite procmap_add_comm. }
    { (* free variables of [A2] are not written to by [C''] *)
    red. intros x H4 H5. apply ghost_sos_fv_mod in GSTEP.
    destruct GSTEP as (FV2 & FV3 & FV4 & FV5).
    apply FV1 in H4. by apply FV3 in H5. }
    { (* assertion [A1] is satisfied with [ph2] and [pm2] *)
    apply ghost_sos_fv_mod in GSTEP.
    destruct GSTEP as (FV2 & FV3 & FV4 & FV5).
    rewrite <- assn_sat_agree with (s1 := s).
    rewrite <- assn_sat_ghost_agree with (g1 := g). done.
    + intros x H2. apply FV5. intro. by apply FV1 with x.
    + intros x H2. apply FV4. intro. by apply FV1 with x. }
    { (* disjointness of [ph1] and [phJ] *)
    apply permheap_disj_add_l with ph2; auto.
    by rewrite permheap_add_comm. }
    { (* disjointness of [ph1 + phJ] and [ph2 + phF] *)
    apply permheap_disj_assoc_l.
    + rewrite permheap_add_comm.
      apply permheap_disj_assoc_r; auto.
    + by rewrite permheap_add_swap_r. }
    { (* disjointness of [pm1] and [pmJ] *)
    apply procmap_disj_add_l with pm2; auto.
    by rewrite procmap_add_comm. }
    { (* disjointness of [pm1 + pmJ] and [pm2 + pmF] *)
    apply procmap_disj_assoc_l.
    + rewrite procmap_add_comm.
      apply procmap_disj_assoc_r; auto.
    + by rewrite procmap_add_swap_r. }
    { (* the composition of [pmC] is correct *)
    rewrite <- H1.
    rewrite procmap_add_swap_r with (pm2 := pm2).
    by repeat rewrite procmap_add_assoc. }
    { (* the composite heap [ph1 + phJ + ph2 + phF] is finite *)
    rewrite <- permheap_add_assoc.
    by rewrite permheap_add_swap_r with (ph2 := phJ). }
    { (* the map [pmC] covers the old snapshot heap *)
    rewrite <- permheap_add_assoc.
    by rewrite permheap_add_swap_r with (ph2 := phJ). }
    { (* the map [pmC] is safe with [ph1 + phJ + ph2 + phF] *)
    rewrite <- permheap_add_assoc.
    by rewrite permheap_add_swap_r with (ph2 := phJ). }
Qed.

Theorem rule_frame (env : ProcEnv) :
  forall basic J A1 A2 A3 C,
  disjoint (assn_fv A3) (cmd_mod C) ->
  csl env basic J A1 C A2 ->
  csl env basic J (Astar A1 A3) C (Astar A2 A3).
Proof.
  intros basic J A1 A2 A3 C FV CSL. red. split.
  (* the program [C] is a user program *)
  - by destruct CSL as (? & _).
  (* the program [C] is safe for any number of steps *)
  - intros ENV n ph pm s g V1 V2 WF SAT.
    destruct CSL as (_ & SAFE).
    destruct SAT as (ph1 & ph2 & D1 & H1 & SAT).
    destruct SAT as (pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
    rewrite <- H1, <- H2.
    apply safe_frame; auto.
    apply SAFE; auto.
    (* validity of [ph1] *)
    + by apply permheap_disj_valid_l in D1.
    (* validity of [pm1] *)
    + by apply procmap_disj_valid_l in D2.
Qed.


(** *** Heap reading *)

Lemma rule_lookup_std (env : ProcEnv) :
  forall basic x E1 q E2 J A,
  ~ In x (expr_fv E1) ->
  ~ In x (expr_fv E2) ->
  ~ assn_fv J x ->
  csl env basic J (Astar (assn_subst x E2 A) (Apointsto PTTstd q E1 E2)) (Cread x E1) (Astar A (Apointsto PTTstd q E1 E2)).
Proof.
  intros basic x E1 q E2 J A FV1 FV2 FV3. red. split; vauto.
  intros ENV [|n] ph pm s g V1 V2 WF SAT. vauto.
  destruct SAT as (ph1 & ph2 & D1 & EQ1 & pm1 & pm2 & D2 & EQ2 & SAT1 & SAT2).
  clarify.

  assert (EQ3 : phc_concr (ph2 (expr_denot E1 s)) = Some (expr_denot E2 s)). {
    unfold assn_sat in SAT2.
    apply phc_concr_le_some with (v := expr_denot E2 s) in SAT2; vauto. }
  assert (EQ4 : phc_concr (permheap_add ph1 ph2 (expr_denot E1 s)) = Some (expr_denot E2 s)). {
    rewrite <- permheap_add_cell.
    apply phc_concr_le_some with (phc1 := ph2 (expr_denot E1 s)); vauto.
    rewrite phc_add_comm. apply phc_le_mono_pos; auto. }

  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    unfold permheap_concr in H4. rewrite <- permheap_add_cell in H4.
    apply phc_concr_le_none with (phc1 := permheap_add ph1 ph2 (expr_denot E1 s)) in H4.
    + apply phc_concr_le_none with (phc1 := PHCstd q (expr_denot E2 s)) in H4; vauto.
    + by apply phc_le_mono_pos.

  (* (3) all heap accesses are in the footprint *)
  - intros l H1. simpl in H1. clarify.
    unfold assn_sat in SAT2.
    apply phc_lt_le_trans with (PHCstd q (expr_denot E2 s)); auto.
    transitivity (ph2 (expr_denot E1 s)); auto.
    rewrite permheap_add_comm. apply phc_le_mono_pos. auto.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP.

    (* [v] equals the evaluation of [E1] *)
    assert (EQ5 : phc_concr (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF (expr_denot E1 s)) = Some (expr_denot E2 s)). {
      apply phc_concr_add, phc_concr_add; auto. }
    assert (EQ6 : expr_denot E2 s = v). {
      cut (Some (expr_denot E2 s) = Some v); try intuition vauto.
      by rewrite <- EQ5, <- H7. }

    clarify.
    exists (permheap_add ph1 ph2), phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, Cskip. intuition vauto.
    { (* the resource invariant [J] is still satisfied *)
    intros _. rewrite assn_sat_upd; auto. }
    apply safe_done.
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. repeat split; vauto.

    { (* satisfiability - left *)
    by rewrite assn_sat_subst in SAT1. }
    { (* satisfiability - right *)
    unfold assn_sat. unfold assn_sat in SAT2.
    repeat rewrite expr_denot_upd; auto. }
Qed.

Lemma rule_lookup_proc (env : ProcEnv) :
  forall basic x E1 q E2 J A,
  ~ In x (expr_fv E1) ->
  ~ In x (expr_fv E2) ->
  ~ assn_fv J x ->
  csl env basic J (Astar (assn_subst x E2 A) (Apointsto PTTproc q E1 E2)) (Cread x E1) (Astar A (Apointsto PTTproc q E1 E2)).
Proof.
  intros basic x E1 q E2 J A FV1 FV2 FV3. red. split; vauto.
  intros ENV [|n] ph pm s g V1 V2 WF SAT. vauto.
  destruct SAT as (ph1 & ph2 & D1 & EQ1 & pm1 & pm2 & D2 & EQ2 & SAT1 & SAT2).
  clarify.

  assert (EQ3 : phc_concr (ph2 (expr_denot E1 s)) = Some (expr_denot E2 s)). {
    unfold assn_sat in SAT2.
    apply phc_concr_le_some with (v := expr_denot E2 s) in SAT2; vauto. }
  assert (EQ4 : phc_concr (permheap_add ph1 ph2 (expr_denot E1 s)) = Some (expr_denot E2 s)). {
    rewrite <- permheap_add_cell.
    apply phc_concr_le_some with (phc1 := ph2 (expr_denot E1 s)); vauto.
    rewrite phc_add_comm. apply phc_le_mono_pos; auto. }

  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    unfold permheap_concr in H4. rewrite <- permheap_add_cell in H4.
    apply phc_concr_le_none with (phc1 := permheap_add ph1 ph2 (expr_denot E1 s)) in H4.
    + apply phc_concr_le_none with (phc1 := PHCproc q (expr_denot E2 s)) in H4; vauto.
    + by apply phc_le_mono_pos.

  (* (3) all heap accesses are in the footprint *)
  - intros l H1. simpl in H1. clarify.
    unfold assn_sat in SAT2.
    apply phc_lt_le_trans with (PHCproc q (expr_denot E2 s)); auto.
    transitivity (ph2 (expr_denot E1 s)); auto.
    rewrite permheap_add_comm. apply phc_le_mono_pos. auto.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP.

    (* [v] equals the evaluation of [E1] *)
    assert (EQ5 : phc_concr (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF (expr_denot E1 s)) = Some (expr_denot E2 s)). {
      apply phc_concr_add, phc_concr_add; auto. }
    assert (EQ6 : expr_denot E2 s = v). {
      cut (Some (expr_denot E2 s) = Some v); try intuition vauto.
      by rewrite <- EQ5, <- H7. }

    clarify.
    exists (permheap_add ph1 ph2), phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, Cskip. intuition vauto.
    { (* the resource invariant [J] is still satisfied *)
    intros _. rewrite assn_sat_upd; auto. }
    apply safe_done.
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. repeat split; vauto.

    { (* satisfiability - left *)
    by rewrite assn_sat_subst in SAT1. }
    { (* satisfiability - right *)
    unfold assn_sat. unfold assn_sat in SAT2.
    repeat rewrite expr_denot_upd; auto. }
Qed.

Lemma rule_lookup_act (env : ProcEnv) :
  forall basic x E1 q E2 J A,
  ~ In x (expr_fv E1) ->
  ~ In x (expr_fv E2) ->
  ~ assn_fv J x ->
  csl env basic J (Astar (assn_subst x E2 A) (Apointsto PTTact q E1 E2)) (Cread x E1) (Astar A (Apointsto PTTact q E1 E2)).
Proof.
  intros basic x E1 q E2 J A FV1 FV2 FV3. red. split; vauto.
  intros ENV [|n] ph pm s g V1 V2 WF SAT. vauto.
  destruct SAT as (ph1 & ph2 & D1 & EQ1 & pm1 & pm2 & D2 & EQ2 & SAT1 & (v' & SAT2)).
  clarify.

  assert (EQ3 : phc_concr (ph2 (expr_denot E1 s)) = Some (expr_denot E2 s)). {
    unfold assn_sat in SAT2.
    apply phc_concr_le_some with (v := expr_denot E2 s) in SAT2; vauto. }
  assert (EQ4 : phc_concr (permheap_add ph1 ph2 (expr_denot E1 s)) = Some (expr_denot E2 s)). {
    rewrite <- permheap_add_cell.
    apply phc_concr_le_some with (phc1 := ph2 (expr_denot E1 s)); vauto.
    rewrite phc_add_comm. apply phc_le_mono_pos; auto. }

  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    unfold permheap_concr in H4. rewrite <- permheap_add_cell in H4.
    apply phc_concr_le_none with (phc1 := permheap_add ph1 ph2 (expr_denot E1 s)) in H4.
    + apply phc_concr_le_none with (phc1 := PHCact q (expr_denot E2 s) v') in H4; vauto.
    + by apply phc_le_mono_pos.

  (* (3) all heap accesses are in the footprint *)
  - intros l H1. simpl in H1. clarify.
    unfold assn_sat in SAT2.
    apply phc_lt_le_trans with (PHCact q (expr_denot E2 s) v'); auto.
    transitivity (ph2 (expr_denot E1 s)); auto.
    rewrite permheap_add_comm. apply phc_le_mono_pos. auto.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP.

    (* [v] equals the evaluation of [E1] *)
    assert (EQ5 : phc_concr (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF (expr_denot E1 s)) = Some (expr_denot E2 s)). {
      apply phc_concr_add, phc_concr_add; auto. }
    assert (EQ6 : expr_denot E2 s = v). {
      cut (Some (expr_denot E2 s) = Some v); try intuition vauto.
      by rewrite <- EQ5, <- H7. }

    clarify.
    exists (permheap_add ph1 ph2), phJ. intuition.
    exists pm, pmJ, pmC. intuition.
    exists g, Cskip. intuition vauto.
    { (* the resource invariant [J] is still satisfied *)
    intros _. rewrite assn_sat_upd; auto. }
    apply safe_done.
    exists ph1, ph2. repeat split; vauto.
    exists pm1, pm2. repeat split; vauto.

    { (* satisfiability - left *)
    by rewrite assn_sat_subst in SAT1. }
    { (* satisfiability - right *)
    unfold assn_sat. exists v'.
    unfold assn_sat in SAT2.
    repeat rewrite expr_denot_upd; auto. }
Qed.

Theorem rule_lookup (env : ProcEnv) :
  forall basic x E1 q E2 J A t,
  ~ In x (expr_fv E1) ->
  ~ In x (expr_fv E2) ->
  ~ assn_fv J x ->
  csl env basic J (Astar (assn_subst x E2 A) (Apointsto t q E1 E2)) (Cread x E1) (Astar A (Apointsto t q E1 E2)).
Proof.
  intros basic x E1 q E2 J A t FV1 FV2 FV3. destruct t.
  - by apply rule_lookup_std.
  - by apply rule_lookup_proc.
  - by apply rule_lookup_act.
Qed.


(** *** Heap writing *)

(** Soundness of the rules for heap writing. In the paper these rules are
    presented as a single rule (for presentational convenience), but here
    we handle heap writing via two separate rules -- one for handling
    points-to ownership predicates of type [PTTstd], and one for [PTTact]. *)

Theorem rule_write_std (env : ProcEnv) :
  forall basic J E1 E2 E3,
  csl env basic J (Apointsto PTTstd perm_full E1 E3) (Cwrite E1 E2) (Apointsto PTTstd perm_full E1 E2).
Proof.
  intros basic J E1 E2 E3. red. split; vauto.
  intros ENV [|n] ph pm s g V1 V2 WF SAT.
  vauto. repeat split; vauto.
	(* (2) absence of faults *)
  - red. intros phF pmF D1 D2 _ _ ABORT.
    inv ABORT. clear ABORT.
    unfold assn_sat in SAT.
    unfold permheap_concr in H4.
    rewrite <- permheap_add_cell in H4.
    apply phc_concr_le_none with (phc1 := PHCstd perm_full (expr_denot E3 s)) in H4; vauto.
    transitivity (ph (expr_denot E1 s)); vauto.
    by apply phc_le_mono_pos.
	(* (3) all heap accesses are in the footprint *)
  - intros l H1. unfold assn_sat in SAT.
    simpl in H1. clarify.
    apply phc_lt_le_trans with (PHCstd perm_full (expr_denot E3 s)); auto.
  (* (4) all heap writes are in footprint *)
  - intros l H1. simpl in H1. clarify.
    unfold assn_sat in SAT.
    apply phc_full_le with (PHCstd perm_full (expr_denot E3 s)); vauto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP. subst l l0 v' v'0.
    unfold assn_sat in SAT.
    apply phc_le_full_eq in SAT; vauto.
    (* [phJ l] is free *)
    assert (H2 : phJ (expr_denot E1 s') = PHCfree). {
      unfold permheap_disj in D1.
      specialize D1 with (expr_denot E1 s').
      apply phc_disj_full_free in D1; vauto.
      rewrite <- SAT. desf. }
    (* [phF l] is free *)
    assert (H3 : phF (expr_denot E1 s') = PHCfree). {
      unfold permheap_disj in D2.
      specialize D2 with (expr_denot E1 s').
      rewrite <- permheap_add_cell in D2.
      rewrite H2 in D2. rewrite phc_add_iden_l in D2.
      apply phc_disj_full_free in D2; vauto.
      rewrite <- SAT. desf. }
    pose (ph' := update ph (expr_denot E1 s') (PHCstd perm_full (expr_denot E2 s'))).
    (* the new snapshot heap equals the old snapshot heap *)
    assert (H4 : permheap_snapshot (permheap_add (permheap_add ph phJ) phF) = permheap_snapshot (permheap_add (permheap_add ph' phJ) phF)). {
      extensionality l. unfold permheap_snapshot.
      repeat rewrite <- permheap_add_cell. subst ph'.
      unfold update. desf. rewrite H2, H3.
      repeat rewrite phc_add_iden_l. rewrite <- SAT. vauto. }
    exists (update ph (expr_denot E1 s') (PHCstd perm_full (expr_denot E2 s'))), phJ.
    repeat split.
    { (* the updated permission heap is disjoint with [phJ] *)
    intro l. unfold update. desf. rewrite H2.
    apply permheap_disj_iden_l. desf. }
    { (* the updated permission heap, together with [phJ], is disjoint with [phF] *)
    intro l. unfold update, permheap_add. desf.
    + rewrite H2, H3, phc_add_iden_l.
      by apply phc_disj_iden_l.
    + by apply D2. }
    { (* heap concretisations match after the heap update *)
    assert (H5 : phc_concr (PHCstd perm_full (expr_denot E2 s')) = Some (expr_denot E2 s')). { simpls. }
    rewrite <- H5. rewrite <- permheap_concr_upd.
    repeat rewrite permheap_add_upd_free; vauto. }
    { (* the updated heap is still finite *)
    by apply heap_finite_upd. }
    { (* if [C] is basic, the snapshot heap has not changed *)
    rewrite permheap_snapshot_upd. simpl.
    extensionality l. unfold update. desf.
    unfold permheap_snapshot. rewrite <- SAT. simpls. }
    exists pm, pmJ, pmC. intuition.
    { (* the map [pmC] covers the updated snapshot heap *)
    subst ph'. by rewrite <- H4. }
    { (* [pmC] is safe wrt. the updated heap *)
    subst ph'. by rewrite <- H4. }
    exists g, Cskip. intuition.
    { (* the ghost semantics can make a matching step *)
    by apply gsos_write with v. }
    { (* the program is safe for another [n] computation steps *)
    apply safe_done. simpls. unfold update. desf. }
Qed.

Theorem rule_write_act (env : ProcEnv) :
  forall basic J E1 E2 E3,
  csl env basic J (Apointsto PTTact perm_full E1 E3) (Cwrite E1 E2) (Apointsto PTTact perm_full E1 E2).
Proof.
  intros basic J E1 E2 E3. red. split; vauto.
  intros ENV [|n] ph pm s g V1 V2 WF SAT.
  vauto. destruct SAT as (v' & SAT).
  repeat split; vauto.
	(* (2) absence of faults *)
  - red. intros phF pmF D1 D2 _ _ ABORT.
    inv ABORT. clear ABORT.
    unfold permheap_concr in H4.
    rewrite <- permheap_add_cell in H4.
    apply phc_concr_le_none with (phc1 := PHCact perm_full (expr_denot E3 s) v') in H4; vauto.
    transitivity (ph (expr_denot E1 s)); vauto.
    by apply phc_le_mono_pos.
	(* (3) all heap accesses are in the footprint *)
  - intros l H1. unfold assn_sat in SAT.
    simpl in H1. clarify.
    apply phc_lt_le_trans with (PHCact perm_full (expr_denot E3 s) v'); auto.
  (* (4) all heap writes are in footprint *)
  - intros l H1. simpl in H1. clarify.
    apply phc_full_le with (PHCact perm_full (expr_denot E3 s) v'); vauto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP. subst l l0 v'0 v'1.
    apply phc_le_full_eq in SAT; vauto.
    (* [phJ l] is free *)
    assert (H2 : phJ (expr_denot E1 s') = PHCfree). {
      unfold permheap_disj in D1.
      specialize D1 with (expr_denot E1 s').
      apply phc_disj_full_free in D1; vauto.
      rewrite <- SAT. desf. }
    (* [phF l] is free *)
    assert (H3 : phF (expr_denot E1 s') = PHCfree). {
      unfold permheap_disj in D2.
      specialize D2 with (expr_denot E1 s').
      rewrite <- permheap_add_cell in D2.
      rewrite H2 in D2. rewrite phc_add_iden_l in D2.
      apply phc_disj_full_free in D2; vauto.
      rewrite <- SAT. desf. }
    pose (ph' := update ph (expr_denot E1 s') (PHCact perm_full (expr_denot E2 s') v')).
    (* the new snapshot heap equals the old snapshot heap *)
    assert (H4 : permheap_snapshot (permheap_add (permheap_add ph phJ) phF) = permheap_snapshot (permheap_add (permheap_add ph' phJ) phF)). {
      extensionality l. unfold permheap_snapshot.
      repeat rewrite <- permheap_add_cell. subst ph'.
      unfold update. desf. rewrite H2, H3.
      repeat rewrite phc_add_iden_l. rewrite <- SAT. vauto. }
    exists (update ph (expr_denot E1 s') (PHCact perm_full (expr_denot E2 s') v')), phJ.
    repeat split.
    { (* the updated permission heap is disjoint with [phJ] *)
    intro l. unfold update. desf. rewrite H2.
    apply permheap_disj_iden_l. desf. }
    { (* the updated permission heap, together with [phJ], is disjoint with [phF] *)
    intro l. unfold update, permheap_add. desf.
    + rewrite H2, H3, phc_add_iden_l.
      by apply phc_disj_iden_l.
    + by apply D2. }
    { (* heap concretisations match after the heap update *)
    assert (H5 : phc_concr (PHCact perm_full (expr_denot E2 s') v') = Some (expr_denot E2 s')). { simpls. }
    rewrite <- H5. rewrite <- permheap_concr_upd.
    repeat rewrite permheap_add_upd_free; vauto. }
    { (* the updated heap is still finite *)
    by apply heap_finite_upd. }
    { (* if [C] is basic, the snapshot heap has not changed *)
    rewrite permheap_snapshot_upd. simpl.
    extensionality l. unfold update. desf.
    unfold permheap_snapshot. rewrite <- SAT. simpls. }
    exists pm, pmJ, pmC. intuition.
    { (* the map [pmC] covers the updated snapshot heap *)
    subst ph'. by rewrite <- H4. }
    { (* [pmC] is safe wrt. the updated heap *)
    subst ph'. by rewrite <- H4. }
    exists g, Cskip. intuition.
    { (* the ghost semantics can make a matching step *)
    by apply gsos_write with v. }
    { (* the program is safe for another [n] computation steps *)
    apply safe_done. simpls. exists v'. unfold update. desf. }
Qed.


(** *** Heap allocation *)

Theorem rule_alloc (env : ProcEnv) :
  forall basic x E J,
  ~ In x (expr_fv E) ->
  ~ assn_fv J x ->
  csl env basic J Atrue (Calloc x E) (Apointsto PTTstd perm_full (Evar x) E).
Proof.
  intros basic x E J FV1 FV2. red. split; vauto.
  intros ENV [|n] ph pm s g V1 V2 WF SAT.
  vauto. repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    apply H4. by apply heap_finite_free.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP.
    unfold permheap_concr in H7.
    (* the heap cell at location [l] is free *)
    assert (H2 : permheap_add (permheap_add ph phJ) phF l = PHCfree). {
      apply phc_concr_none_free in H7; auto. by apply phc_add_valid. }
    unfold permheap_add in H2.
    apply phc_iden_split in H2. destruct H2 as (H2 & H3).
    apply phc_iden_split in H2. destruct H2 as (H2 & H4).
    pose (ph' := update ph l (PHCstd perm_full v)).
    (* the new snapshot heap equals the old snapshot heap *)
    assert (H5 : permheap_snapshot (permheap_add (permheap_add ph phJ) phF) = permheap_snapshot (permheap_add (permheap_add ph' phJ) phF)). {
      extensionality l'. unfold permheap_snapshot.
      repeat rewrite <- permheap_add_cell. subst ph'.
      unfold update. desf. rewrite H2, H3, H4.
      repeat rewrite phc_add_iden_l. vauto. }
    exists ph', phJ. intuition subst ph'.
    { (* the updated heap is disjoint with [phJ] *)
    intro l'. unfold update. desf.
	  rewrite H4. by apply phc_disj_iden_l. }
    { (* the updated heap, together with [phJ], is disjoint with [phF] *)
    intro l'. unfold update, permheap_add. desf.
    + rewrite H3, H4. rewrite phc_add_iden_l.
	    by apply phc_disj_iden_l.
	  + by apply D2. }
    { (* the heap concretisations match after the heap update *)
    assert (H6 : phc_concr (PHCstd perm_full v) = Some v). { simpls. }
    rewrite <- H6. rewrite <- permheap_concr_upd.
    repeat rewrite permheap_add_upd_free; vauto. }
    { (* the updated heap is still finite *)
    by apply heap_finite_upd. }
    { (* if [C] is basic, the snapshot heap has not changed *)
    rewrite permheap_snapshot_upd. simpl.
    extensionality l'. unfold update. desf.
    unfold permheap_snapshot. rewrite H2. simpls. }
    exists pm, pmJ, pmC. intuition.
    { (* the map [pmC] covers the new snapshot heap *)
    by rewrite <- H5. }
    { (* the map [pmC] is safe with the new snapshot heap *)
    by rewrite <- H5. }
    exists g, Cskip. repeat split; auto.
    { (* the ghost semantics can make a matching step *)
    constructor. unfold permheap_concr, permheap_add.
    rewrite H2, H3, H4. by repeat rewrite phc_add_iden_l. }
    { (* the resource invariant [J] is still satisfied *)
    unfold invariant_sat in INV.
    red. simpls. intros _. intuition.
    by apply assn_sat_upd. }
    { (* the program is safe for another [n] steps *)
    apply safe_done. simpls.
    repeat rewrite update_apply.
    intuition. apply Qcle_refl.
    by rewrite expr_denot_upd. }
Qed.


(** *** Heap disposal *)

Theorem rule_dispose (env : ProcEnv) :
  forall basic E1 E2 J,
  csl env basic J (Apointsto PTTstd perm_full E1 E2) (Cdispose E1) Atrue.
Proof.
  intros basic E1 E2 J. red. split; vauto.
  intros ENV [|n] ph pm s g V1 V2 WF SAT.
  vauto. unfold assn_sat in SAT.
  repeat split; vauto.
	(* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    unfold permheap_concr in H4.
    assert (H2 : permheap_add ph phF (expr_denot E1 s) = PHCfree). {
      apply phc_concr_none_free in H4; vauto.
      by apply permheap_add_valid. }
    rewrite <- permheap_add_cell in H2.
    apply phc_iden_split in H2.
    destruct H2 as (H2 & H3).
    rewrite H2 in SAT. simpls.
  (* (3) all heap accesses are in the footprint *)
  - intros l H1. simpl in H1. clarify.
    apply phc_lt_le_trans with (PHCstd perm_full (expr_denot E2 s)); vauto.
  (* (4) all heap writes are in footprint *)
  - intros l H1. simpl in H1. clarify.
    apply phc_le_full_eq in SAT; vauto.
    rewrite <- SAT. vauto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. clear STEP. subst l l0.
    (* [ph l] is full *)
    assert (H2 : ph (expr_denot E1 s') = PHCstd perm_full (expr_denot E2 s')). {
      apply phc_le_full_eq in SAT; vauto. } clear SAT.
    (* [phJ l] is free *)
    assert (H3 : phJ (expr_denot E1 s') = PHCfree). {
      unfold permheap_disj in D1.
      specialize D1 with (expr_denot E1 s').
      apply phc_disj_full_free in D1; vauto.
      rewrite H2. desf. }
    (* [phF l] is free *)
    assert (H4 : phF (expr_denot E1 s') = PHCfree). {
      unfold permheap_disj in D2.
      specialize D2 with (expr_denot E1 s').
      rewrite <- permheap_add_cell in D2.
      rewrite H3 in D2. rewrite phc_add_iden_l in D2.
      apply phc_disj_full_free in D2; vauto.
      rewrite H2. desf. }
    pose (ph' := update ph (expr_denot E1 s') PHCfree).
    (* the new snapshot heap equals the old snapshot heap *)
    assert (H5 : permheap_snapshot (permheap_add (permheap_add ph phJ) phF) = permheap_snapshot (permheap_add (permheap_add ph' phJ) phF)). {
      extensionality l'. unfold permheap_snapshot.
      repeat rewrite <- permheap_add_cell. subst ph'.
      unfold update. desf. rewrite H2, H3, H4.
      repeat rewrite phc_add_iden_l. vauto. }
    exists ph', phJ. intuition subst ph'.
    { (* the updated heap is disjoint with [phJ] *)
    intro l'. unfold update. desf.
    apply phc_disj_iden_r. by rewrite H3. }
    { (* the updated heap, together with [phJ], is disjoint with [phF] *)
    intro l'. unfold update, permheap_add. desf.
    + rewrite H3, H4, phc_add_iden_l.
      by apply phc_disj_iden_r.
    + by apply D2. }
    { (* the heap concretisations should be proper also after the update *)
    assert (H6 : phc_concr PHCfree = None). { simpls. }
    rewrite <- H6. rewrite <- permheap_concr_upd.
    repeat rewrite permheap_add_upd_free; vauto. }
    { (* the heap should be finite after the update *)
    by apply heap_finite_upd. }
    { (* if [C] is basic, the snapshot heap has not changed *)
    rewrite permheap_snapshot_upd. simpl.
    extensionality l'. unfold update. desf.
    unfold permheap_snapshot. rewrite H2. simpls. }
    exists pm, pmJ, pmC. intuition.
    { (* the map [pmC] covers the new snapshot heap *)
    by rewrite <- H5. }
    { (* the map [pmC] is safe with the new snapshot heap *)
    by rewrite <- H5. }
    exists g, Cskip. intuition vauto.
    apply safe_done. simpls.
Qed.


(** *** Parallel composition *)

(* Note: although the proof is not very difficult, it is very long, because
   it requires a lot of puzzling to get all the 'disjointness' obligations right. *)
Lemma safe_par (env : ProcEnv) :
  forall n basic C1 C2 ph1 ph2 pm1 pm2 s g J A1 A2,
  permheap_disj ph1 ph2 ->
  procmap_disj pm1 pm2 ->
  cmd_wf (Cpar C1 C2) ->
  disjoint (cmd_fv C1) (cmd_mod C2) ->
  disjoint (assn_fv A1) (cmd_mod C2) ->
  disjoint (assn_fv J) (cmd_mod C2) ->
  disjoint (cmd_fv C2) (cmd_mod C1) ->
  disjoint (assn_fv A2) (cmd_mod C1) ->
  disjoint (assn_fv J) (cmd_mod C1) ->
  safe n env basic C1 ph1 pm1 s g J A1 ->
  safe n env basic C2 ph2 pm2 s g J A2 ->
  safe n env basic (Cpar C1 C2) (permheap_add ph1 ph2) (procmap_add pm1 pm2) s g J (Astar A1 A2).
Proof.
  induction n as [|n IH]; vauto.
  intros basic C1 C2 ph1 ph2 pm1 pm2 s g J A1 A2.
  intros D1 D2 WF FV1 FV2 FV3 FV4 FV5 FV6 SAFE1 SAFE2.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT; clear ABORT.
    (* case 1 : no faults in [C1] *)
    + rewrite permheap_add_assoc, procmap_add_assoc in H5.
      destruct SAFE1 as (_ & ABORT1 & _).
      apply ABORT1 in H5; auto.
      * by apply permheap_disj_assoc_l.
      * by apply procmap_disj_assoc_l.
      * by rewrite <- permheap_add_assoc.
      * by rewrite <- procmap_add_assoc.
    (* case 2 : no faults in [C2] *)
    + rewrite permheap_add_comm with ph1 ph2 in H5.
      rewrite procmap_add_comm with (pm1 := pm1)(pm2 := pm2) in H5.
      rewrite permheap_add_assoc, procmap_add_assoc in H5.
      destruct SAFE2 as (_ & ABORT2 & _).
      apply ABORT2 in H5; auto.
      * apply permheap_disj_assoc_l; auto.
        by rewrite permheap_add_comm.
      * apply procmap_disj_assoc_l; auto.
        by rewrite procmap_add_comm.
      * rewrite <- permheap_add_assoc.
        by rewrite permheap_add_comm with ph2 ph1.
      * rewrite <- procmap_add_assoc.
        by rewrite procmap_add_comm with (pm1 := pm2)(pm2 := pm1).
    (* case 3: no deadlocks *)
    + inversion WF as (WF1 & WF2 & LOCKED).
      apply LOCKED. intuition.
    (* case 4: no data races - scenario 1 *)
    + apply H7. red. intros l F7 F8.
      destruct SAFE1 as (_ & _ & _ & WR & _).
      destruct SAFE2 as (_ & _ & ACC & _ & _).
      apply WR in F7. apply ACC in F8. clear ACC WR.
      unfold permheap_disj in D1.
      specialize D1 with l.
      apply phc_disj_full_free in D1; vauto.
      rewrite D1 in F8. by apply phc_lt_irrefl in F8.
    (* case 5 : no data races - scenario 2 *)
    + apply H7. red. intros l F7 F8.
      destruct SAFE1 as (_ & _ & ACC & _ & _).
      destruct SAFE2 as (_ & _ & _ & WR & _).
      apply ACC in F7. apply WR in F8. clear ACC WR.
      unfold permheap_disj in D1.
      specialize D1 with l. symmetry in D1.
      apply phc_disj_full_free in D1; vauto.
      rewrite D1 in F7. by apply phc_lt_irrefl in F7.
  (* (3) all heap accesses are in footprint *)
  - intros l F7. destruct F7 as [F7 | F7].
    (* heap accesses in [C1] are in the footprint *)
    + destruct SAFE1 as (_ & _ & ACC & _ & _).
      apply ACC in F7. clear ACC.
      rewrite <- permheap_add_cell.
      apply phc_lt_le_trans with (ph1 l); vauto.
      by apply phc_le_mono_pos.
    (* heap accesses in [C2] are in the footprint *)
    + destruct SAFE2 as (_ & _ & ACC & _ & _).
      apply ACC in F7. clear ACC.
      rewrite <- permheap_add_cell.
      apply phc_lt_le_trans with (ph2 l); vauto.
      rewrite phc_add_comm. apply phc_le_mono_pos; auto.
  (* (4) all heap writes are in footprint *)
  - intros l F7. destruct F7 as [F7 | F7].
    (* heap writes in [C1] are in the footprint *)
    + destruct SAFE1 as (_ & _ & _ & WR & _).
      apply WR in F7. clear WR.
      rewrite <- permheap_add_cell.
      apply phc_full_add; vauto.
    (* heap writes in [C2] are in the footprint *)
    + destruct SAFE2 as (_ & _ & _ & WR & _).
      apply WR in F7. clear WR.
      rewrite <- permheap_add_cell.
      rewrite phc_add_comm. apply phc_full_add; auto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP; clear STEP.
    (* step in [C1] *)
    + rewrite permheap_add_swap_r with (ph2 := ph2) in H4.
      rewrite permheap_add_assoc in H4.
      apply SAFE1 with (pmJ := pmJ)(pmF := procmap_add pm2 pmF)(pmC := pmC) in H4; clear SAFE1; auto.
      destruct H4 as (ph' & phJ' & D7 & D8 & H2 & FIN3 & BASIC1 & H4).
      destruct H4 as (pm' & pmJ' & pmC' & D9 & D10 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE2 & H4).
      destruct H4 as (g' & C'' & H4 & GSTEP & INV1 & SAFE1). clarify.
      exists (permheap_add ph' ph2), phJ'. intuition.
      { (* disjointness of [ph' + ph2] and [pjJ'] *)
      apply permheap_disj_add_r in D8; auto.
      rewrite permheap_add_comm in D8.
      apply permheap_disj_assoc_l in D8; auto.
      apply permheap_disj_add_l with ph1; auto.
      apply permheap_disj_add_l with phJ; auto.
      by rewrite permheap_add_comm. }
      { (* disjointness of [ph' + ph2 + phJ'] and [phF] *)
      rewrite permheap_add_swap_r.
      apply permheap_disj_assoc_r; auto.
      apply permheap_disj_add_l with ph1; auto.
      apply permheap_disj_add_l with phJ; auto.
      by rewrite permheap_add_comm. }
      { (* heap concretisation is proper *)
      rewrite permheap_add_swap_r with (ph2 := ph2).
      by rewrite permheap_add_assoc. }
      { (* if [C1] is basic, the snapshot heap has not changed *)
      apply permheap_snapshot_disj_add_l; auto.
      apply permheap_disj_add_l with phJ; auto.
      - rewrite H2. by symmetry.
      - apply permheap_disj_add_r with phF; auto.
        + apply permheap_disj_add_l with ph1; auto.
          apply permheap_disj_add_l with phJ; auto.
          by rewrite permheap_add_comm.
        + rewrite permheap_add_comm with phJ ph'. by rewrite H2. }
      exists (procmap_add pm' pm2), pmJ', pmC'. intuition.
      { (* disjointness of [pm' + pm2] and [pmJ'] *)
      apply procmap_disj_add_r in D10; auto.
      rewrite procmap_add_comm in D10.
      apply procmap_disj_assoc_l in D10; auto.
      apply procmap_disj_add_l with pm1; auto.
      apply procmap_disj_add_l with pmJ; auto.
      by rewrite procmap_add_comm. }
      { (* disjointness of [pm' + pm2 + pmJ'] and [pmF] *)
      rewrite procmap_add_swap_r.
      apply procmap_disj_assoc_r; auto.
      apply procmap_disj_add_l with pm1; auto.
      apply procmap_disj_add_l with pmJ; auto.
      by rewrite procmap_add_comm. }
      { (* composition of [pmC] is proper *)
      rewrite <- H3.
      by rewrite procmap_add_swap_r with (pm2 := pm2). }
      { (* the process map has not changed, given that [C1] is basic *)
      by rewrite H5. }
      { (* the map [pmC'] covers the new snapshot heap *)
      rewrite permheap_add_swap_r with (ph2 := ph2).
      by rewrite permheap_add_assoc. }
      { (* the map [pmC'] is safe with the new snapshot heap *)
      rewrite permheap_add_swap_r with (ph2 := ph2).
      by rewrite permheap_add_assoc. }
      exists g', (Cpar C'' C2). intuition vauto.
      { (* ghost semantics can make a step *)
      rewrite permheap_add_swap_r with (ph2 := ph2).
      rewrite permheap_add_assoc.
      apply gsos_par_l; auto.
      by rewrite <- cmd_locked_plain. }
      { (* the resource invariant [J] is still satisfied *)
      unfold invariant_sat in INV1.
      red. simpl. intro H9.
      apply not_or_and in H9.
      destruct H9 as (H9 & H10).
      by apply INV1. }
      apply IH; intuition vauto.
      { (* disjointness of [ph'] and [ph2] *)
      apply permheap_disj_add_l with phJ'; auto.
      rewrite permheap_add_comm.
      apply permheap_disj_add_r with phF; auto.
      apply permheap_disj_add_l with ph1; auto.
      apply permheap_disj_add_l with phJ; auto.
      by rewrite permheap_add_comm. }
      { (* disjointness of [pm'] and [pm2] *)
      apply procmap_disj_add_l with pmJ'; auto.
      rewrite procmap_add_comm.
      apply procmap_disj_add_r with pmF; auto.
      apply procmap_disj_add_l with pm1; auto.
      apply procmap_disj_add_l with pmJ; auto.
      by rewrite procmap_add_comm. }
      { (* the program [Cpar C'' C2] is well-formed *)
      destruct WF as (WF1 & WF2 & LOCKED).
      constructor; repeat split; auto.
      (* the program [C''] is well-formed *)
      * by apply ghost_sos_wf_pres in GSTEP.
      (* the programs [C''] and [C2] are not both locked *)
      * intro H9. destruct H9 as (H9 & H10).
        by rewrite cmd_locked_plain in H8. }
      { (* free variables in [C''] are not modified in [C2] *)
      red. intros x FV7 FV8. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (FV9 & FV10 & FV11 & FV12).
      apply FV9 in FV7. by apply FV1 with x. }
      { (* free variables in [C2] are not modified in [C''] *)
      red. intros x FV7 FV8. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (FV9 & FV10 & FV11 & FV12).
      apply FV10 in FV8. by apply FV4 with x. }
      { (* free variables in [A2] are not modified in [C''] *)
      red. intros x FV7 FV8. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (FV9 & FV10 & FV11 & FV12).
      apply FV10 in FV8. by apply FV5 with x. }
      { (* free variables in [J] are not modified in [C''] *)
      red. intros x FV7 FV8. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (FV9 & FV10 & FV11 & FV12).
      apply FV10 in FV8. by apply FV6 with x. }
      { (* program is safe for [n] more steps *)
      apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (_ & _ & FV9 & FV10).
      apply safe_agree with s; auto.
      intros x FV7. apply FV9. intro FV8. by apply FV5 with x.
      intros x FV7. apply FV9. intro FV8. by apply FV6 with x.
      intros x FV7. apply FV9. intro FV8. by apply FV4 with x.
      apply safe_agree_ghost with g; auto.
      intros x FV7. apply FV10. intro FV8. by apply FV5 with x.
      intros x FV7. apply FV10. intro FV8. by apply FV6 with x.
      intros x FV7. apply FV10. intro FV8. by apply FV4 with x.
      apply safe_mono with (S n). apply le_n_Sn. simpls. }
      { (* disjointness of [ph1] and [phJ] *)
      apply permheap_disj_add_l with ph2; auto.
      by rewrite permheap_add_comm. }
      { (* disjointness of [ph1 + phJ] and [ph2 + phF] *)
      apply permheap_disj_assoc_l.
      rewrite permheap_add_comm.
      apply permheap_disj_assoc_r; auto.
      by rewrite permheap_add_swap_r. }
      { (* disjointness of [pm1] and [pmJ] *)
      apply procmap_disj_add_l with pm2; auto.
      by rewrite procmap_add_comm. }
      { (* disjointness of [pm1 + pmJ] and [pm2 + pmF] *)
      apply procmap_disj_assoc_l.
      rewrite procmap_add_comm.
      apply procmap_disj_assoc_r; auto.
      by rewrite procmap_add_swap_r. }
      { (* composition of [pmC] is proper *)
      rewrite <- H1.
      rewrite procmap_add_swap_r with (pm2 := pm2).
      by repeat rewrite procmap_add_assoc. }
      { (* the resource invariant [J] was satisfied before the step *)
      unfold invariant_sat in INV.
      red. simpls. intro LOCKED. apply INV.
      apply and_not_or. split; auto.
      by rewrite cmd_locked_plain in H8. }
      { (* the permission heap [ph1 + ph + ph2 + phF] is finite *)
      rewrite <- permheap_add_assoc.
      by rewrite permheap_add_swap_r with ph1 phJ ph2. }
      { (* the map [pmC] covers the old snapshot heap *)
      rewrite <- permheap_add_assoc.
      by rewrite permheap_add_swap_r with (ph2 := phJ). }
      { (* the map [pmC] is safe with the old snapshot heap *)
      rewrite <- permheap_add_assoc.
      by rewrite permheap_add_swap_r with (ph2 := phJ). }
    (* step in [C2] *)
    + rewrite permheap_add_comm with ph1 ph2 in H4.
      rewrite permheap_add_swap_r with (ph2 := ph1) in H4.
      rewrite permheap_add_assoc in H4.
      apply SAFE2 with (pmJ := pmJ)(pmF := procmap_add pm1 pmF)(pmC := pmC) in H4; clear SAFE2; auto.
      destruct H4 as (ph' & phJ' & D7 & D8 & H2 & FIN3 & BASIC1 & H4).
      destruct H4 as (pm' & pmJ' & pmC' & D9 & D10 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE2 & H4).
      destruct H4 as (g' & C'' & H4 & GSTEP & INV1 & SAFE2). clarify.
      exists (permheap_add ph1 ph'), phJ'. intuition.
      { (* disjointness of [ph1 + ph'] and [phF] *)
      apply permheap_disj_assoc_r; auto.
      apply permheap_disj_add_l with phF; auto.
      symmetry. apply permheap_disj_add_l with ph2; auto.
      rewrite permheap_add_comm.
      apply permheap_disj_add_l with phJ; auto.
      by rewrite permheap_add_comm.
      symmetry. by rewrite permheap_add_comm with phF ph1. }
      { (* disjointness of [ph1 + ph' + phJ'] and [phF] *)
      rewrite permheap_add_comm with ph1 ph'.
      rewrite permheap_add_swap_r with (ph2 := ph1).
      apply permheap_disj_assoc_r; auto.
      apply permheap_disj_add_l with ph2; auto.
      apply permheap_disj_add_l with phJ; auto.
      symmetry. by rewrite permheap_add_comm.
      rewrite permheap_add_comm.
      by rewrite permheap_add_comm with ph2 ph1. }
      { (* heap concretisation is proper *)
      rewrite permheap_add_comm with ph1 ph'.
      rewrite permheap_add_swap_r with (ph2 := ph1).
      by rewrite permheap_add_assoc. }
      { (* if [C1] is basic, the snapshot heap has not changed *)
      apply permheap_snapshot_disj_add_r; auto.
      apply permheap_disj_add_l with phJ; auto.
      - rewrite H2. by symmetry.
      - apply permheap_disj_add_r with phF; auto.
        + apply permheap_disj_add_l with ph2; auto.
          apply permheap_disj_add_l with phJ; auto.
          * symmetry. by rewrite permheap_add_comm.
          * rewrite permheap_add_comm.
            by rewrite permheap_add_comm with ph2 ph1.
        + rewrite permheap_add_comm with phJ ph'. by rewrite H2. }
      exists (procmap_add pm1 pm'), pmJ', pmC'. intuition.
      { (* disjointness of [pm1 + pm'] and [pmF] *)
      apply procmap_disj_assoc_r; auto.
      apply procmap_disj_add_l with pmF; auto.
      symmetry. apply procmap_disj_add_l with pm2; auto.
      rewrite procmap_add_comm.
      apply procmap_disj_add_l with pmJ; auto.
      by rewrite procmap_add_comm.
      symmetry. by rewrite procmap_add_comm with (pm1 := pmF)(pm2 := pm1). }
      { (* disjointness of [pm1 + pm' + pmJ'] and [pmF] *)
      rewrite procmap_add_comm with (pm1 := pm1)(pm2 := pm').
      rewrite procmap_add_swap_r with (pm2 := pm1).
      apply procmap_disj_assoc_r; auto.
      apply procmap_disj_add_l with pm2; auto.
      apply procmap_disj_add_l with pmJ; auto.
      symmetry. by rewrite procmap_add_comm.
      rewrite procmap_add_comm.
      by rewrite procmap_add_comm with (pm1 := pm2)(pm2 := pm1). }
      { (* composition of [pmC] is proper *)
      rewrite procmap_add_comm with (pm1 := pm1)(pm2 := pm').
      rewrite <- H3.
      by rewrite procmap_add_swap_r with (pm2 := pm1). }
      { (* the process map has not changed, given that [C1] is basic *)
      by rewrite H5. }
      { (* the map [pmC'] covers the new snapshot heap *)
      rewrite permheap_add_comm with ph1 ph'.
      rewrite permheap_add_swap_r with (ph2 := ph1).
      by rewrite permheap_add_assoc. }
      { (* the map [pmC'] is safe with the new snapshot heap *)
      rewrite permheap_add_comm with ph1 ph'.
      rewrite permheap_add_swap_r with (ph2 := ph1).
      by rewrite permheap_add_assoc. }
      exists g', (Cpar C1 C''). intuition vauto.
      { (* ghost semantics can make a step *)
      rewrite permheap_add_comm with ph1 ph2.
      rewrite permheap_add_swap_r with (ph2 := ph1).
      rewrite permheap_add_assoc.
      apply gsos_par_r; auto.
      by rewrite <- cmd_locked_plain. }
      { (* the resource invariant [J] is still satisfied *)
      unfold invariant_sat in INV.
      red. simpls. intro H.
      apply not_or_and in H.
      destruct H as (H' & H). clear H'.
      by apply INV1. }
      apply IH; intuition vauto.
      { (* disjointness of [ph1] and [ph'] *)
      symmetry.
      apply permheap_disj_add_l with phJ'; auto.
      rewrite permheap_add_comm.
      apply permheap_disj_add_r with phF; auto.
      apply permheap_disj_add_l with ph2; auto.
      rewrite permheap_add_comm.
      apply permheap_disj_add_l with phJ; auto.
      by rewrite permheap_add_comm. }
      { (* disjointness of [pm1] and [pm'] *)
      symmetry.
      apply procmap_disj_add_l with pmJ'; auto.
      rewrite procmap_add_comm.
      apply procmap_disj_add_r with pmF; auto.
      apply procmap_disj_add_l with pm2; auto.
      rewrite procmap_add_comm.
      apply procmap_disj_add_l with pmJ; auto.
      by rewrite procmap_add_comm. }
      { (* the program [Cpar C1 C''] is well-formed *)
      destruct WF as (WF1 & WF2 & LOCKED).
      constructor; repeat split; auto.
      (* the program [C''] is well-formed *)
      * by apply ghost_sos_wf_pres in GSTEP.
      (* the programs [C1] and [C''] are not both locked *)
      * intro H9. destruct H9 as (H9 & H10).
        by rewrite cmd_locked_plain in H8. }
      { (* free variables in [C1] are not modified in [C''] *)
      red. intros x FV7 FV8. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (FV9 & FV10 & FV11 & FV12).
      apply FV10 in FV8. by apply FV1 with x. }
      { (* free variables in [A1] are not modified in [C''] *)
      red. intros x FV7 FV8. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (FV9 & FV10 & FV11 & FV12).
      apply FV10 in FV8. by apply FV2 with x. }
      { (* free variables in [J] are not modified in [C''] *)
      red. intros x FV7 FV8. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (FV9 & FV10 & FV11 & FV12).
      apply FV10 in FV8. by apply FV3 with x. }
      { (* free variables in [J] are not modified in [C''] *)
      red. intros x FV7 FV8. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (FV9 & FV10 & FV11 & FV12).
      apply FV9 in FV7. by apply FV4 with x. }
      { (* program is safe for [n] more steps *)
      apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (_ & _ & FV9 & FV10).
      apply safe_agree with s; auto.
      intros x FV7. apply FV9. intro FV8. by apply FV2 with x.
      intros x FV7. apply FV9. intro FV8. by apply FV3 with x.
      intros x FV7. apply FV9. intro FV8. by apply FV1 with x.
      apply safe_agree_ghost with g; auto.
      intros x FV7. apply FV10. intro FV8. by apply FV2 with x.
      intros x FV7. apply FV10. intro FV8. by apply FV3 with x.
      intros x FV7. apply FV10. intro FV8. by apply FV1 with x.
      apply safe_mono with (S n). apply le_n_Sn. simpls. }
      { (* disjointness of [ph2] and [phJ] *)
      apply permheap_disj_add_l with ph1; auto. }
      { (* disjointness of [ph2 + phJ] and [ph1 + phF] *)
      apply permheap_disj_assoc_l.
      rewrite permheap_add_comm.
      apply permheap_disj_assoc_r; auto.
      symmetry. by rewrite permheap_add_comm.
      rewrite permheap_add_swap_r.
      by rewrite permheap_add_comm with ph2 ph1. }
      { (* disjointness of [pm2] and [pmJ] *)
      apply procmap_disj_add_l with pm1; auto. }
      { (* disjointness of [pm2 + pmJ] and [pm1 + pmF] *)
      apply procmap_disj_assoc_l.
      rewrite procmap_add_comm.
      apply procmap_disj_assoc_r; auto.
      symmetry. by rewrite procmap_add_comm.
      rewrite procmap_add_swap_r.
      by rewrite procmap_add_comm with (pm1 := pm2)(pm2 := pm1). }
      { (* composition of [pmC] is proper *)
      rewrite <- H1.
      rewrite procmap_add_comm with (pm1 := pm1)(pm2 := pm2).
      rewrite procmap_add_swap_r with (pm2 := pm1).
      by repeat rewrite procmap_add_assoc. }
      { (* the resource invariant [J] was satisfied before the step *)
      unfold invariant_sat in INV.
      red. simpls. intro H9. apply INV.
      apply and_not_or. split; vauto.
      by rewrite cmd_locked_plain in H8. }
      { (* the heap [ph2 + phJ + ph1 + phF] is finite *)
      rewrite <- permheap_add_assoc.
      rewrite permheap_add_swap_r with ph2 phJ ph1.
      by rewrite permheap_add_comm with ph2 ph1. }
      { (* the map [pmC] covers the old snapshot heap *)
      rewrite <- permheap_add_assoc.
      rewrite permheap_add_swap_r with (ph2 := phJ).
      by rewrite permheap_add_comm with ph2 ph1. }
      { (* the map [pmC] is safe with the old snapshot heap *)
      rewrite <- permheap_add_assoc.
      rewrite permheap_add_swap_r with (ph2 := phJ).
      by rewrite permheap_add_comm with ph2 ph1. }
    (* [C1] and [C2] are both empty *)
    + symmetry in H3, H4.
      apply plain_skip in H3.
      apply plain_skip in H4. clarify.
      exists (permheap_add ph1 ph2), phJ. intuition.
      exists (procmap_add pm1 pm2), pmJ, pmC. intuition.
      exists g, Cskip. intuition.
      { (* the ghost semantics can make a matching step *)
      * constructor. }
      { (* the resource invariant [J] is satisfied *)
      unfold invariant_sat in INV.
      red. simpls. intuition. }
      { (* the program is safe for [n] more steps *)
      apply safe_done. simpls.
      exists ph1, ph2. intuition.
      exists pm1, pm2. intuition. }
Qed.

Theorem rule_par (env : ProcEnv) :
  forall basic C1 C2 J A1 A2 A1' A2',
  disjoint (cmd_fv C1) (cmd_mod C2) ->
  disjoint (assn_fv A1') (cmd_mod C2) ->
  disjoint (assn_fv J) (cmd_mod C2) ->
  disjoint (cmd_fv C2) (cmd_mod C1) ->
  disjoint (assn_fv A2') (cmd_mod C1) ->
  disjoint (assn_fv J) (cmd_mod C1) ->
  csl env basic J A1 C1 A1' ->
  csl env basic J A2 C2 A2' ->
  csl env basic J (Astar A1 A2) (Cpar C1 C2) (Astar A1' A2').
Proof.
  intros basic C1 C2 J A1 A2 A1' A2' FV1 FV2 FV3 FV4 FV5 FV6 CSL1 CSL2.
  red. split; vauto.
  (* the program [Cpar C1 C2] is a user program *)
  - constructor.
    + by destruct CSL1 as (? & _).
    + by destruct CSL2 as (? & _).
  (* the program [Cpar C1 C2] is safe for [n] computation steps *)
  - intros ENV n ph pm s g V1 V2 WF SAT.
    destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
    rewrite <- H1, <- H2. apply safe_par; auto.
    (* the program [C1] is safe for [n] computation steps *)
    + destruct CSL1 as (_ & SAFE).
      apply SAFE; auto.
      * by apply permheap_disj_valid_l in D1.
      * by apply procmap_disj_valid_l in D2.
      * by destruct WF as (WF1 & WF2 & LOCKED).
    (* the program [C2] is safe for [n] computation steps *)
    + destruct CSL2 as (_ & SAFE).
      apply SAFE; auto.
      * by apply permheap_disj_valid_r in D1.
      * by apply procmap_disj_valid_r in D2.
      * by destruct WF as (WF1 & WF2 & LOCKED).
Qed.


(** *** Existential quantification *)

Open Scope Z_scope.

Theorem rule_ex (env : ProcEnv) :
  forall basic C J (A1 A2 : Val -> Assn),
    (forall x, csl env basic J (A1 x) C (A2 x)) ->
  csl env basic J (Aex A1) C (Aex A2).
Proof.
  intros basic C J A1 A2 CSL.
  red. split; auto.
  (* the program [C] is a user program *)
  - specialize CSL with 0.
    by destruct CSL as (USER & _).
  (* the program [C] is safe for any number of steps *)
  - intros ENV n ph pm s g V1 V2 WF SAT.
    destruct SAT as (v & SAT).
    apply safe_conseq with (A2 v); vauto.
    by apply CSL.
Qed.

Close Scope Z_scope.


(** *** Share rule *)

Lemma safe_share (env : ProcEnv) :
  forall n C ph1 ph2 pm1 pm2 s g J A1 A2,
  permheap_disj ph1 ph2 ->
  procmap_disj pm1 pm2 ->
  invariant_sat ph2 pm2 s g C A2 ->
  safe n env False C ph1 pm1 s g (Astar J A2) A1 ->
  safe n env False C (permheap_add ph1 ph2) (procmap_add pm1 pm2) s g J (Astar A1 A2).
Proof.
  induction n as [|n IH]; vauto.
  intros C ph1 ph2 pm1 pm2 s g J A1 A2 D1 D2 SAT SAFE.
  repeat split; vauto.
  (* (1) terminating programs *)
  - intro H1. clarify.
    exists ph1, ph2. intuition.
    exists pm1, pm2. intuition.
    destruct SAFE as (TERM & _).
    by apply TERM.
  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    rewrite permheap_add_assoc in ABORT.
    rewrite procmap_add_assoc in ABORT.
    destruct SAFE as (_ & ABORT1 & _).
    apply ABORT1 in ABORT; auto.
    (* [ph1] is disjoint with [ph2 + phF] *)
    + by apply permheap_disj_assoc_l.
    (* [pm1] is disjoint with [pm2 + pmF] *)
    + by apply procmap_disj_assoc_l.
    (* [ph1 + ph2 + phF] is finite *)
    + by rewrite <- permheap_add_assoc.
    (* [pm1 + pm2 + pmF] is finite *)
    + by rewrite <- procmap_add_assoc.
  (* (3) all shared-memory reads of [C] are in the footprint *)
  - intros l H1.
    destruct SAFE as (_ & _ & ACC & _).
    apply ACC in H1. clear ACC.
    rewrite <- permheap_add_cell.
    apply phc_lt_le_trans with (ph1 l); vauto.
    by apply phc_le_mono_pos.
  (* (4) all shared-memory writes of [C] are in the footprint *)
  - intros l H1. destruct SAFE as (_ & _ & _ & WRITES & _).
    apply WRITES in H1. clear WRITES.
    rewrite <- permheap_add_cell.
    apply phc_full_add; vauto.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    rewrite permheap_add_assoc with ph1 ph2 phJ in STEP.
    cut (cmd_locked C' \/ ~ cmd_locked C'); [|apply classic].
    intro H. destruct H as [LOCKED | LOCKED].
    (* the program [C'] is locked *)
    + destruct SAFE as (_ & _ & _ & _ & SAFE).
      apply SAFE with (pmJ := procmap_add pm2 pmJ)(pmF := pmF)(pmC := pmC) in STEP; clear SAFE; auto.
      destruct STEP as (ph' & phJ' & D7 & D8 & H2 & FIN3 & BASIC1 & STEP).
      destruct STEP as (pm' & pmJ' & pmC' & D9 & D10 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE2 & STEP).
      destruct STEP as (g' & C'' & H4 & GSTEP & INV1 & SAFE). clarify.
      exists ph', phJ'. intuition.
      exists pm', pmJ', pmC'. intuition.
      exists g', C''. intuition.
      { (* the ghost semantics can make a matching step *)
      by repeat rewrite permheap_add_assoc in *. }
      { (* the resource invariant [J] is still satisfied *)
      unfold invariant_sat in INV1.
      red. intro H2. apply INV1 in H2.
      clear INV1. simpl in H2.
      destruct H2 as (ph1' & ph2' & D11 & H4 & pm1' & pm2' & D12 & H5 & SAT1 & SAT2).
      rewrite <- H4, <- H5. by apply assn_sat_weaken. }
      { (* the program is safe for [n] more steps *)
      rewrite <- permheap_add_iden_l with ph'.
      rewrite <- procmap_add_iden_l with pm'.
      apply IH; auto.
      (* [ph'] is disjoint with the identity heap *)
      + apply permheap_disj_iden_r.
        by apply permheap_disj_valid_l in D7.
      (* [pm'] is disjoint with the identity process map *)
      + apply procmap_disj_iden_r.
        by apply procmap_disj_valid_l in D9.
      (* [A2] is satisfied as a resource invariant *)
      + red. clarify. intro H2.
        by rewrite cmd_locked_plain in LOCKED. }
      by apply permheap_disj_assoc_l.
      by rewrite <- permheap_add_assoc.
      by apply procmap_disj_assoc_l.
      by rewrite <- procmap_add_assoc.
      by rewrite <- procmap_add_assoc.
      { (* the resource invariant was satisfied before the step *)
      red. intro H2. clarify.
      unfold invariant_sat in SAT, INV.
      assert (H3 : assn_sat ph2 pm2 s g A2). { by apply SAT in H2. }
      assert (H4 : assn_sat phJ pmJ s g J). { by apply INV in H2. }
      exists phJ, ph2. intuition.
      + symmetry. by apply permheap_disj_add_l with ph1.
      + by rewrite permheap_add_comm.
      + exists pmJ, pm2. intuition.
        * symmetry. by apply procmap_disj_add_l with pm1.
        * by rewrite procmap_add_comm. }
    { (* the heap [ph1 + ph2 + phJ + phF] is finite *)
    by rewrite <- permheap_add_assoc. }
    { (* the map [pmC] covers the old snapshot heap *)
    by rewrite <- permheap_add_assoc. }
    { (* the map [pmC] is safe with the old snapshot heap *)
    by rewrite <- permheap_add_assoc. }
    (* the program [C'] is not locked *)
    + destruct SAFE as (_ & _ & _ & _ & SAFE).
      apply SAFE with (pmJ := procmap_add pm2 pmJ)(pmF := pmF)(pmC := pmC) in STEP; clear SAFE; auto.
      destruct STEP as (ph' & phJ' & D7 & D8 & H2 & FIN3 & BASIC1 & STEP).
      destruct STEP as (pm' & pmJ' & pmC' & D9 & D10 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE2 & STEP).
      destruct STEP as (g' & C'' & H4 & GSTEP & INV1 & SAFE). clarify.
      rewrite cmd_locked_plain in LOCKED.
      unfold invariant_sat in INV1.
      apply INV1 in LOCKED. clear INV1.
      simpl in LOCKED.
      destruct LOCKED as (phJ'' & ph2' & D11 & H2 & pmJ'' & pm2' & D12 & H4 & SAT1 & SAT2).
      clarify.
	    exists (permheap_add ph' ph2'), phJ''. intuition.
	    { (* disjointness of [ph' + ph2'] and [phJ''] *)
	    apply permheap_disj_assoc_r; auto.
	    by rewrite permheap_add_comm. }
	    { (* disjointness of [ph' + ph2' + phJ''] and [phF] *)
	    rewrite permheap_add_swap_r.
	    by rewrite permheap_add_assoc. }
	    { (* heap concretisation is proper *)
	    rewrite permheap_add_swap_r with (ph2 := ph2').
	    by repeat rewrite permheap_add_assoc. }
	    exists (procmap_add pm' pm2'), pmJ'', pmC'. intuition.
	    { (* disjointness of [pm' + pm2'] and [pmJ''] *)
	    apply procmap_disj_assoc_r; auto.
	    rewrite procmap_add_comm. by rewrite H4. }
	    { (* disjointness of [pm' + pm2' + pmJ''] and [pmF] *)
	    rewrite procmap_add_swap_r, procmap_add_assoc.
	    by rewrite H4. }
	    { (* structure of [pmC] is proper *)
	    rewrite <- H3, <- H4.
	    rewrite procmap_add_swap_r with (pm2 := pm2').
	    by repeat rewrite procmap_add_assoc. }
      { (* the map [pmC'] covers the new snapshot heap *)
	    rewrite permheap_add_swap_r with (ph2 := ph2').
	    repeat rewrite permheap_add_assoc.
      by repeat rewrite permheap_add_assoc in COV2. }
      { (* the map [pmC'] is safe with the new snapshot heap *)
	    rewrite permheap_add_swap_r with (ph2 := ph2').
	    repeat rewrite permheap_add_assoc.
      by repeat rewrite permheap_add_assoc in PSAFE2. }
	    exists g', C''. intuition.
      { (* the ghost semantics can make a matching step *)
	    by rewrite permheap_add_assoc with ph1 ph2 phJ. }
      { (* the resource invariant [J] is still maintained *)
	    red. intuition. }
	    apply IH; vauto.
	    { (* disjointness of [ph'] and [ph2'] *)
	    apply permheap_disj_add_r with phJ''; auto.
	    by rewrite permheap_add_comm. }
	    { (* disjointness of [pm'] and [pm2'] *)
	    apply procmap_disj_add_r with pmJ''; auto.
	    by rewrite procmap_add_comm, H4. }
	    { (* disjointness of [ph1] and [ph2 + phJ] *)
	    apply permheap_disj_add_l with phF; auto.
	    symmetry. apply permheap_disj_add_l with ph2; auto.
	    rewrite permheap_add_comm.
	    apply permheap_disj_add_l with phJ; auto.
	    rewrite permheap_add_comm; auto.
	    apply permheap_disj_assoc_r; auto.
	    apply permheap_disj_assoc_l; auto.
	    symmetry. by rewrite <- permheap_add_assoc. }
	    by rewrite <- permheap_add_assoc.
	    { (* disjointness of [pm1] and [pm2 + pmJ] *)
	    apply procmap_disj_add_l with pmF; auto.
	    symmetry. apply procmap_disj_add_l with pm2; auto.
	    rewrite procmap_add_comm.
	    apply procmap_disj_add_l with pmJ; auto.
	    rewrite procmap_add_comm; auto.
	    apply procmap_disj_assoc_r; auto.
	    apply procmap_disj_assoc_l; auto.
	    symmetry. by rewrite <- procmap_add_assoc. }
	    by rewrite <- procmap_add_assoc.
	    by rewrite <- procmap_add_assoc.
	    { (* satisfiability of the postcondition *)
	    exists phJ, ph2. intuition.
	    symmetry. apply permheap_disj_add_l with ph1; auto.
	    by rewrite permheap_add_comm.
	    exists pmJ, pm2. intuition.
	    symmetry. apply procmap_disj_add_l with pm1; auto.
	    by rewrite procmap_add_comm. }
      { (* the heap [ph1 + ph2 + phJ + phF] is finite *)
      by rewrite <- permheap_add_assoc. }
      { (* the map [pmC] covers the old snapshot heap *)
      by rewrite <- permheap_add_assoc. }
      { (* the map [pmC] is safe with the old snapshot heap *)
      by rewrite <- permheap_add_assoc. }
Qed.

Theorem rule_share (env : ProcEnv) :
  forall C J A1 A2 A3,
  csl env False (Astar J A3) A1 C A2 ->
  csl env False J (Astar A1 A3) C (Astar A2 A3).
Proof.
  intros C J A1 A2 A3 CSL.
  red. split; vauto.
  (* the program [C] is a user program *)
  - by destruct CSL as (USER & _).
  (* the program [C] is safe for any number of steps *)
  - intros ENV n ph pm s g V1 V2 WF SAT.
    simpl in SAT.
    destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
    rewrite <- H1, <- H2.
    apply safe_share; auto.
    (* the resource invariant [Ar] is satisfied *)
    + red. intro H. exact SAT2.
    (* the program is safe with [Astar J Ar] the resource invariant *)
    + destruct CSL as (_ & SAFE).
      apply SAFE; auto.
      * by apply permheap_disj_valid_l in D1.
      * by apply procmap_disj_valid_l in D2.
Qed.


(** *** Atomic rule *)

Lemma safe_atom (env : ProcEnv) :
  forall n C ph pm s g J A,
  safe n env False C ph pm s g Atrue (Astar A J) ->
  safe n env False (Cinatom C) ph pm s g J A.
Proof.
  induction n as [|n IH]; vauto.
  intros C ph pm s g J A SAFE.
  repeat split; vauto.
  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    destruct SAFE as (_ & AB & _).
    by apply AB in H4.
  (* (3) all shared-memory accesses are in the footprint *)
  - intros l H1. destruct SAFE as (_ & _ & ACC & _).
    apply ACC. simpls.
  (* (4) all shared-memory writes are in the footprint *)
  - intros l H1. destruct SAFE as (_ & _ & _ & WRITES & _).
    apply WRITES. simpls.
  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP; clear STEP.
    (* the program [C] is not empty *)
    + destruct SAFE as (_ & _ & _ & _ & SAFE).
      apply SAFE with (pmJ := pmJ)(pmF := pmF)(pmC := pmC) in H3; vauto.
      clear SAFE.
      destruct H3 as (ph' & phJ' & D7 & D8 & H2 & FIN3 & BASIC1 & H3).
      destruct H3 as (pm' & pmJ' & pmC' & D9 & D10 & H3 & FIN4 & WS2 & BASIC2 & COV2 & PSAFE2 & H4).
      destruct H4 as (g' & C'' & H4 & GSTEP & INV1 & SAFE). clarify.
      exists ph', phJ'. intuition.
      exists pm', pmJ', pmC'. intuition.
      exists g', (Cinatom C''). intuition.
      { (* the ghost semantics can make a matching step *)
      by constructor. }
      { (* the resource invariant [J] is still maintained *)
      red. simpls. }
    (* the program [C] is empty *)
    + symmetry in H3. apply plain_skip in H3.
      clarify. destruct SAFE as (TERM & _).
      assert (H3 : assn_sat ph pm s' g (Astar A J)). { by apply TERM. }
      clear TERM. simpl in H3.
      destruct H3 as (ph1 & ph2 & D7 & H2 & pm1 & pm2 & D8 & H3 & SAT1 & SAT2).
      clarify.
      exists ph1, (permheap_add ph2 phJ). intuition.
      { (* disjointness of [ph1] and [ph2 + phJ] *)
      apply permheap_disj_add_r with phF; auto.
      apply permheap_disj_add_l with ph1; auto.
      apply permheap_disj_assoc_l; auto.
      by rewrite <- permheap_add_assoc.
      apply permheap_disj_assoc_l.
      apply permheap_disj_assoc_l; auto.
      by rewrite <- permheap_add_assoc. }
      by rewrite <- permheap_add_assoc.
      by rewrite <- permheap_add_assoc.
      exists pm1, (procmap_add pm2 pmJ), pmC. intuition.
      { (* disjointness of [pm1] and [pm2 + pmJ] *)
      apply procmap_disj_add_r with pmF; auto.
      apply procmap_disj_add_l with pm1; auto.
      apply procmap_disj_assoc_l; auto.
      by rewrite H3.
      rewrite <- procmap_add_assoc. by rewrite H3.
      apply procmap_disj_assoc_l.
      apply procmap_disj_assoc_l; auto. by rewrite H3.
      rewrite <- procmap_add_assoc. by rewrite H3. }
      { (* [pm1 + pm2 + pmJ] is disjoint with [pmF] *)
      rewrite <- procmap_add_assoc. by rewrite H3. }
      { (* the composition [pm1 + pm2 + pmJ + pmF] describes [pmC] *)
      rewrite <- procmap_add_assoc. by rewrite H3. }
      { (* the map [pmC] covers the old snapshot heap *)
      by rewrite <- permheap_add_assoc. }
      { (* the map [pmC] is safe with the old snapshot heap *)
      by rewrite <- permheap_add_assoc. }
      exists g, Cskip. intuition vauto.
      { (* the resource invariant is still satisfied *)
      red. intros H'. clear H'.
      apply assn_sat_weaken; auto.
      by apply permheap_disj_add_l with ph1.
      apply procmap_disj_add_l with pm1; auto.
      by rewrite H3. }
      by apply safe_done.
Qed.

Theorem rule_atom (env : ProcEnv) :
  forall C J A1 A2,
  csl env False Atrue (Astar A1 J) C (Astar A2 J) ->
  csl env False J A1 (Catomic C) A2.
Proof.
  intros C J A1 A2 CSL. red. split.
  (* the program [Catomic C] is a _user program_ *)
  - destruct CSL as (WF & _). vauto.
  (* the program [Catomic C] is _safe_ for any number of steps *)
  - intros ENV [|n] ph pm s g V1 V2 WF SAT. vauto.
    repeat split; vauto.
    (* absence of faults *)
    + red. intros phF pmF D1 D2 FIN1 FIN2 ABORT.
      inv ABORT.
    (* program step *)
    + simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE STEP.
      inv STEP. unfold invariant_sat in INV.
      assert (H2 : assn_sat phJ pmJ s' g J). { apply INV. intuition. }
      clear INV.
      exists (permheap_add ph phJ), permheap_iden. intuition.
      by rewrite permheap_add_iden_l.
      by rewrite permheap_add_iden_l.
      exists (procmap_add pm pmJ), procmap_iden, pmC. intuition.
      by rewrite procmap_add_iden_l.
      by rewrite procmap_add_iden_l.
      { (* the map [pmC] covers the old snapshot heap *)
      by rewrite permheap_add_iden_l. }
      { (* the map [pmC] is safe with the old snapshot heap *)
      by rewrite permheap_add_iden_l. }
      exists g, (Cinatom C). intuition vauto.
      { (* the resource invariant [J] is still maintained *)
      red. ins. }
      apply safe_atom.
      destruct CSL as ( _ & SAFE).
      apply SAFE; vauto.
      { (* [ph + phJ] is valid *)
      by apply permheap_add_valid. }
      { (* [pm + pmJ] is valid *)
      by apply procmap_add_valid. }
      exists ph, phJ. intuition vauto.
      exists pm, pmJ. intuition vauto.
Qed.


(** *** Process init rule *)

Theorem rule_proc_init (env : ProcEnv) :
  forall x p xs J (f1 f2 : ProcVar -> Expr),
  let b1 := fst (env p) in
  let P := body p in
  let B := pbexpr_convert b1 f2 in
  let fq := fun _ => perm_full in
    (forall y, In y (pbexpr_fv b1) -> In y xs) ->
  ~ assn_fv J x ->
  ~ (exists y : ProcVar, In y xs /\ In x (expr_fv (f1 y))) ->
  ~ (exists y : ProcVar, In y xs /\ In x (expr_fv (f2 y))) ->
  csl env False J
    (Astar (Aiter (pointsto_iter xs fq f1 f2 PTTstd)) (Aplain B))
    (Cproc x p xs f1)
    (Astar (Astar (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) (Aproc x perm_full p P xs f1)) (Aplain B)).
Proof.
  simpl. intros x p xs J f1 f2.
  red. intros FV1 FV2 FV3 FV4. split; vauto.
  intros ENV [|n] ph pm s g V1 V2 WF SAT. vauto.
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  set (F1 := expr_denot_map f1 s : ProcVar -> Val).
  set (F2 := expr_denot_map f2 s : ProcVar -> Val).
  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT. clear ABORT.
    apply H5. by apply procmap_finite_free.

  (* (3) all shared-memory accesses are in the footprint *)
  - intros l (y & H1 & H3). clarify.
    unfold pointsto_iter in SAT1.
    apply assn_iter_In_l with (eq_dec := Z.eq_dec)(x0 := y) in SAT1; auto.
    + destruct SAT1 as (ph1' & ph2' & D3 & H3 & pm1' & pm2' & D4 & H4 & SAT1 & SAT1').
      unfold assn_sat in SAT1.
      apply phc_full_le in SAT1; vauto.
      apply phc_lt_le_trans with ((permheap_add ph1' ph2') (expr_denot (f1 y) s)); vauto.
      * apply phc_lt_weaken; vauto. by apply phc_lt_full_free.
      * apply phc_le_mono_pos. vauto.
      * by apply permheap_disj_valid_l in D3.
    + by apply permheap_disj_valid_l in D1.
    + by apply procmap_disj_valid_l in D2.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. generalize SAT1. intro SAT1'.
    apply pointsto_iter_conv_std_proc in SAT1.

    (* the process map has a free entry (due to its finiteness) *)
    assert (H6 : exists pid, pmC pid = PMfree). { by apply procmap_finite_free. }
    destruct H6 as (pid & H6).

    (* TODO description *)
    pose (ls := map (expr_denot_map f1 s') xs : list Loc).
    pose (ph1' := permheap_conv_proc_mult ph1 ls).
    replace (map (expr_denot_map f1 s') xs) with ls in SAT1; auto.
    replace (permheap_conv_proc_mult ph1 ls) with ph1' in SAT1; auto.

    (* [ph1 l] is a full standard cell, and [ph2 l], [phJ l] and [phF l] are empty for every location [l] in [ls] *)
    assert (HV1 : forall y : ProcVar, In y xs -> ph1 (F1 y) = PHCstd perm_full (F2 y)). {
      intros y HV1. apply pointsto_iter_sat_single_std with (x0 := y) in SAT1'; auto.
      apply phc_le_full_eq in SAT1'; vauto. by apply permheap_disj_valid_l in D1. }
    assert (HVL1 : forall l : Loc, In l ls -> exists v, ph1 l = PHCstd perm_full v). {
      intros l HLV1. subst ls. apply in_map_iff in HLV1.
      destruct HLV1 as (y & ? & HLV1). clarify. exists (F2 y). by apply HV1. }
    assert (HV2 : forall y : ProcVar, In y xs -> ph2 (F1 y) = PHCfree). {
      intros y HV2. red in D1. specialize D1 with (F1 y).
      rewrite HV1 in D1; auto. apply phc_disj_full_free in D1; vauto. }
    assert (HVL2 : forall l, In l ls -> ph2 l = PHCfree). {
      intros l HVL2. subst ls. apply in_map_iff in HVL2.
      destruct HVL2 as (y & ? & HVL2). clarify. by apply HV2. }
    assert (HV3 : forall y : ProcVar, In y xs -> phJ (F1 y) = PHCfree). {
      intros y HV3. red in D3. specialize D3 with (F1 y).
      rewrite <- permheap_add_cell in D3. rewrite HV1, HV2 in D3; auto.
      apply phc_disj_full_free in D3; vauto. }
    assert (HVL3 : forall l, In l ls -> phJ l = PHCfree). {
      intros l HVL3. subst ls. apply in_map_iff in HVL3.
      destruct HVL3 as (y & ? & HVL3). clarify. by apply HV3. }
    assert (HV4 : forall y : ProcVar, In y xs -> phF (F1 y) = PHCfree). {
      intros y HV4. red in D4. specialize D4 with (F1 y).
      repeat rewrite <- permheap_add_cell in D4. rewrite HV1, HV2, HV3 in D4; auto.
      apply phc_disj_full_free in D4; vauto. }
    assert (HVL4 : forall l, In l ls -> phF l = PHCfree). {
      intros l HVL4. subst ls. apply in_map_iff in HVL4.
      destruct HVL4 as (y & ? & HVL4). clarify. by apply HV4. }
    assert (HV5 : forall y : ProcVar, In y xs -> ph1' (F1 y) = PHCproc perm_full (F2 y)). {
      intros y HV5. subst ph1'. rewrite permheap_conv_proc_mult_apply; vauto.
      - rewrite HV1; auto.
      - by apply in_map. }
    assert (HVL5 : forall l : Loc, In l ls -> exists v, ph1' l = PHCproc perm_full v). {
      intros l HVL5. subst ls. apply in_map_iff in HVL5.
      destruct HVL5 as (y & ? & HVL5). clarify. apply HV5 in HVL5.
      exists (F2 y). vauto. }

    (* the heap [ph1'] is disjoint in every composition in which [ph1] is also disjoint *)
    assert (DISJ1 : permheap_disj ph1' ph2). {
      rewrite <- permheap_conv_proc_mult_free with ls ph2; auto.
      subst ph1'. by apply permheap_conv_proc_mult_disj. }
    assert (DISJ2 : permheap_disj (permheap_add ph1' ph2) phJ). {
      rewrite <- permheap_conv_proc_mult_free with ls ph2; auto.
      rewrite <- permheap_conv_proc_mult_free with ls phJ; auto.
      subst ph1'. rewrite <- permheap_conv_proc_mult_add; vauto.
      by apply permheap_conv_proc_mult_disj. }
    assert (DISJ3 : permheap_disj (permheap_add (permheap_add ph1' ph2) phJ) phF). {
      rewrite <- permheap_conv_proc_mult_free with ls ph2; auto.
      rewrite <- permheap_conv_proc_mult_free with ls phJ; auto.
      rewrite <- permheap_conv_proc_mult_free with ls phF; auto.
      subst ph1'. repeat rewrite <- permheap_conv_proc_mult_add; vauto.
      by apply permheap_conv_proc_mult_disj. }

    (* some results on the concrete- and snapshot values of [ph1] with respect to locations in [ls] *)
    assert (HS1 : forall y : ProcVar, In y xs -> phc_concr (ph1 (F1 y)) = Some (F2 y)). {
      intros y HS1. rewrite HV1; auto. }
    assert (HSL1 : forall l : Loc, In l ls -> exists v, phc_concr (ph1 l) = Some v). {
      intros l HSL1. apply HVL1 in HSL1. destruct HSL1 as (v & HSL1). exists v. by rewrite HSL1. }
    assert (HS2 : forall y : ProcVar, In y xs -> phc_snapshot (ph1 (F1 y)) = None). {
      intros y HS2. rewrite HV1; auto. }
    assert (HSL2 : forall l : Loc, In l ls -> phc_snapshot (ph1 l) = None). {
      intros l HSL2. apply HVL1 in HSL2. destruct HSL2 as (v & HSL2). by rewrite HSL2. }
    assert (HS3 : forall y : ProcVar, In y xs -> phc_snapshot (ph1' (F1 y)) = Some (F2 y)). {
      intros y HS3. rewrite HV5; auto. }
    assert (HSL3 : forall l : Loc, In l ls -> exists v, phc_snapshot (ph1' l) = Some v). {
      intros l HSL3. apply HVL5 in HSL3. destruct HSL3 as (v & HSL3). exists v. by rewrite HSL3. }

    exists (permheap_add ph1' ph2), phJ. intuition vauto.

    { (* the heap concretisation is proper *)
    rewrite <- permheap_conv_proc_mult_free with (xs := ls)(ph := ph2) at 1; auto.
    rewrite <- permheap_conv_proc_mult_free with (xs := ls)(ph := phJ) at 1; auto.
    rewrite <- permheap_conv_proc_mult_free with (xs := ls)(ph := phF) at 1; auto.
    subst ph1'. repeat rewrite <- permheap_conv_proc_mult_add; vauto.
    by rewrite permheap_conv_proc_mult_concr. }

    (* the entries [pm1 pid], [pm2 pid], [pmJ pid] and [pmF pid] are all free *)
    assert (PDISJ1 : procmap_add (procmap_add pm pmJ) pmF pid = PMfree). {
      apply pmv_eq_free with (pmC pid); auto. }
    apply pmv_add_free in PDISJ1. destruct PDISJ1 as (PDISJ1 & PDISJ2).
    apply pmv_add_free in PDISJ1. destruct PDISJ1 as (PDISJ1 & PDISJ3).
    assert (PDISJ4 : procmap_add pm1 pm2 pid = PMfree). {
      apply pmv_eq_free with (pm pid); auto. }
    apply pmv_add_free in PDISJ4. destruct PDISJ4 as (PDISJ4 & PDISJ5).

    pose (pm' := update pm pid (PMelem perm_full p (body p) xs F1)).
    pose (pmC' := update pmC pid (PMelem perm_full p (body p) xs F1)).
    exists pm', pmJ, pmC'. repeat split; auto.

    { (* the process maps [pm'] and [pmJ] are disjoint *)
    subst pm'. intro pid'. unfold update. desf.
    rewrite PDISJ3. by apply pmv_disj_iden_l. }

    { (* the process maps [pm' + pmJ] and [pmF] are disjoint *)
    subst pm'. intro pid'. rewrite <- procmap_add_pmv. unfold update. desf.
    - rewrite PDISJ2, PDISJ3. rewrite pmv_add_iden_l. by apply pmv_disj_iden_l.
    - by apply D6. }

    { (* the composition [pm' + pmJ + pmF] equals [pmC] *)
    subst pmC'. intro pid'. unfold update. desf.
    - repeat rewrite <- procmap_add_pmv.
      rewrite PDISJ2, PDISJ3. repeat rewrite pmv_add_iden_l.
      subst pm'. unfold update. desf.
    - unfold procmap_eq in H1. specialize H1 with pid'.
      rewrite <- H1. repeat rewrite <- procmap_add_pmv.
      repeat apply pmv_add_eq_l. subst pm'. unfold update. desf. }

    { (* [pmC'] is finite *)
    subst pmC'. by apply procmap_finite_upd. }

    { (* [pmC'] is well-structured *)
    subst pmC'. apply procmap_ws_upd; vauto.
    intros pid' l K1 ACC1 ACC2. simpl in ACC1.
    apply COV1 in ACC2. destruct ACC2 as (v & ACC2).
    unfold permheap_snapshot in ACC2. repeat rewrite <- permheap_add_cell in ACC2.
    rewrite HVL2, HVL3, HVL4 in ACC2; vauto. repeat rewrite phc_add_iden_l in ACC2.
    apply in_map_iff in ACC1. destruct ACC1 as (y & ACC1' & ACC1). vauto.
    apply pointsto_iter_sat_single_std with (x0 := y) in SAT1'; vauto.
    apply phc_le_full_eq in SAT1'; vauto.
    - subst F1. unfold expr_denot_map in ACC2.
      rewrite <- SAT1' in ACC2. vauto.
    - by apply permheap_disj_valid_l in D1. }

    { (* if the program is basic, then the process map has not changed *)
    intro. contradiction. }

    { (* the map [pmC'] covers the new snapshot heap *)
    subst pmC'. apply procmap_covers_upd.

    (* the new process maps entry is covered in the new snapshot heap *)
    - intros l H13. simpl in H13. subst F1. generalize H13. intro H13'.
      apply in_map_iff in H13. destruct H13 as (y & H13 & H14). vauto.
      apply pointsto_iter_sat_single_proc with (x0 := y) in SAT1; vauto.
      apply phc_le_full_eq in SAT1; vauto.
      + exists (expr_denot (f2 y) s'). unfold permheap_snapshot.
        repeat rewrite <- permheap_add_cell.
        rewrite HVL2, HVL3, HVL4; vauto. repeat rewrite phc_add_iden_l.
        subst ph1' ls. unfold expr_denot_map at 2.
        rewrite <- SAT1. by vauto.
      + apply permheap_conv_proc_mult_valid.
        by apply permheap_disj_valid_l in D1.

    (* all existing process map entries are still covered in the new snapshot heap *)
    - apply procmap_covers_subheap with (permheap_snapshot (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF)); vauto.
      intros l v H13. subst ph1'.
      rewrite <- permheap_conv_proc_mult_free with (xs := ls)(ph := ph2) at 1; auto.
      rewrite <- permheap_conv_proc_mult_free with (xs := ls)(ph := phJ) at 1; auto.
      rewrite <- permheap_conv_proc_mult_free with (xs := ls)(ph := phF) at 1; auto.
      repeat rewrite <- permheap_conv_proc_mult_add; vauto.
      unfold permheap_snapshot in *.
      assert (K1 : In l ls \/ ~ In l ls). { by apply classic. }
      destruct K1 as [K1 | K1].
      + repeat rewrite <- permheap_add_cell in H13.
        rewrite HVL2, HVL3, HVL4 in H13; vauto. repeat rewrite phc_add_iden_l in H13.
        subst ls. apply in_map_iff in K1. destruct K1 as (y & K1 & K2). vauto.
        apply pointsto_iter_sat_single_std with (x0 := y) in SAT1'; vauto.
        apply phc_le_full_eq in SAT1'; vauto.
        * subst F1. unfold expr_denot_map in H13.
          rewrite <- SAT1' in H13. by vauto.
        * by apply permheap_disj_valid_l in D1.
      + rewrite <- permheap_conv_proc_mult_pres; vauto. }

    { (* the map [pmC'] is safe with the new snapshot heap *)
    subst pmC'. intro pid'. unfold update. desf.

    (* the new entry is safe *)
    - red. intros ps IN1. apply ENV. unfold assn_sat in SAT2. 
      rewrite bexpr_denot_conv with (ps := ps) in SAT2; auto. intros y IN2.
      assert (IN3 : In y xs). { by apply FV1. }
      assert (PS1 : phc_snapshot (ph1' (F1 y)) = Some (ps y)). {
        rewrite <- IN1; auto. rewrite HS3; auto.
        symmetry. unfold permheap_snapshot. repeat rewrite <- permheap_add_cell.
        rewrite HV2, HV3, HV4; auto. repeat rewrite phc_add_iden_l.
        by apply HS3. }
      assert (PS2 : Some (ps y) = Some (F2 y)). {
        rewrite <- PS1. by apply HS3. }
      vauto.

    (* all existing entries are still safe *)
    - apply pmv_safe_heap_acc with (permheap_snapshot (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF)); auto.
      intros l IN1. unfold permheap_snapshot.
      repeat apply phc_snapshot_disj_add_l; auto.

      (* the location [l] can not be in [ls] *)
      assert (IN2 : exists v, phc_snapshot (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF l) = Some v). {
        red in COV1. specialize COV1 with pid'. red in COV1.
        apply COV1 in IN1. clear COV1. destruct IN1 as (v & IN1). vauto. }
      assert (IN3 : ~ In l ls). {
        intro IN3. generalize IN3. intro IN4.
        apply HSL2 in IN3. destruct IN2 as (v & IN2).
        cut (phc_snapshot (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF l) = None); intuition vauto.
        repeat rewrite <- permheap_add_cell. rewrite HVL2, HVL3, HVL4; vauto.
        by repeat rewrite phc_add_iden_l. }

      subst ph1'. by rewrite <- permheap_conv_proc_mult_pres. }

    exists (update g x pid), Cskip. repeat split; vauto.

    { (* the resource invariant is still maintained *)
    unfold invariant_sat in INV.
    red. simpls. intros _. intuition.
    by apply assn_sat_upd_ghost. }

    apply safe_done. exists ph1', ph2. repeat split.

    { (* [ph1'] is disjoint with [ph2] *)
    subst ph1'. rewrite <- permheap_conv_proc_mult_free with ls ph2; auto.
    by apply permheap_conv_proc_mult_disj. }

    pose (pm1' := update pm1 pid (PMelem perm_full p (body p) xs F1)).
    exists pm1', pm2. repeat split; auto.

    { (* [pm1'] is disjoint with [pm2] *)
    subst pm1'. intro pid'. unfold update. desf.
    rewrite PDISJ5. apply pmv_disj_iden_l. vauto. }

    { (* the addition [pm1' + pm2] equals [pm'] *)
    intro pid'. rewrite <- procmap_add_pmv.
    subst pm'. unfold update. desf.
    - rewrite PDISJ5. rewrite pmv_add_iden_l.
      subst pm1'. unfold update. desf.
    - unfold procmap_eq in H2. specialize H2 with pid'.
      rewrite <- H2. rewrite <- procmap_add_pmv.
      apply pmv_add_eq_l. subst pm1'. unfold update. desf. }

    exists ph1', permheap_iden. repeat split.

    { (* [ph1'] is disjoint with the identity heap *)
    apply permheap_disj_iden_l. subst ph1'.
    apply permheap_conv_proc_mult_valid.
    by apply permheap_disj_valid_l in D1. }

    { (* [ph1' + iden] equals [ph1'] (which is trivial) *)
    by rewrite permheap_add_iden_l. }

    exists procmap_iden, pm1'. repeat split; vauto.

    { (* [pm1'] is disjoint with the identity process map *)
    apply procmap_disj_iden_r. subst pm1'.
    intro pid'. unfold update. desf.
    by apply procmap_disj_valid_l in D2. }

    { (* [iden + pm1'] equals [pm1'] (which is trivial) *)
    by rewrite procmap_add_iden_r. }

    { (* the iterated separating conjunction part of the postcondition is satisfied *)
    apply pointsto_iter_conv_std_proc; vauto.
    rewrite assn_sat_upd_ghost.
    - apply assn_sat_pointsto_iter_indep with pm1; vauto.
    - intro FV. rewrite assn_fv_pointsto_iter in FV.
      destruct FV as (y & V3 & V4).
      destruct V4 as [V4 | V4]; vauto.
      + apply FV3. exists y. vauto.
      + apply FV4. exists y. vauto. }

    { (* the process predicate part of the postcondition holds *)
    unfold assn_sat. exists PMfree. split; vauto.
    rewrite update_apply. rewrite pmv_add_iden_l.
    subst pm1'. rewrite update_apply. vauto. }
Qed.


(** *** Process end rule *)

Theorem rule_proc_end (env : ProcEnv) :
  forall x p xs J (f1 f2 : ProcVar -> Expr)(P : Proc),
  let b2 := snd (env p) in
  let B := pbexpr_convert b2 f2 in
  let fq := fun _ => perm_full in
    (forall y, In y (pbexpr_fv b2) -> In y xs) ->
  proc_term P ->
  csl env False J
    (Astar (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) (Aproc x perm_full p P xs f1))
    (Cendproc x)
    (Astar (Aiter (pointsto_iter xs fq f1 f2 PTTstd)) (Aplain B)).
Proof.
  intros x p xs J f1 f2 P b2. red. intros FV1 PTERM. split; vauto.
  intros ENV [|n] ph pm s g V1 V2 WF SAT. vauto.
  set (F1 := expr_denot_map f1 s : ProcVar -> Val).
  set (F2 := expr_denot_map f2 s : ProcVar -> Val).
  destruct SAT as (ph1 & ph2 & D1 & H1 & pm1 & pm2 & D2 & H2 & SAT1 & SAT2).
  repeat split; vauto.

  (* (2) absence of faults - two cases *)
  - red. intros phF pmF D3 D4 FIN1 FIN2 ABORT.
    inv ABORT; clear ABORT.

    (* case 1: [(pm + pmF) pid] can not be empty *)
    + apply H5. clear H5. unfold assn_sat in SAT2.
      destruct SAT2 as (pmv & D5 & H1).
      apply pmv_full_add; vauto. left.
      unfold procmap_eq in H2. specialize H2 with (g x).
      rewrite <- H2, <- procmap_add_pmv.
      apply pmv_full_add; vauto. right.
      rewrite H1. apply pmv_full_add; vauto.

    (* case 2: the process entry at [(pm + pmF) pid] must terminate *)
    + apply H6. clear H6. unfold assn_sat in SAT2.
      destruct SAT2 as (pmv & D5 & SAT2).
      rewrite pmv_full_exp_l in SAT2; vauto.
      unfold procmap_eq in H2. specialize H2 with (g x).
      rewrite <- procmap_add_pmv in H2. rewrite SAT2 in H2.
      rewrite pmv_full_exp_r in H2; vauto.
      { (* [P] terminates *)
      rewrite <- procmap_add_pmv in H0. rewrite <- H2 in H0.
      rewrite pmv_full_exp_l in H0; vauto.
      - simpl in H0. destruct H0 as (K1 & K2 & K3 & K4 & K5).
        clarify. by rewrite <- K3.
      - unfold procmap_disj in D4. specialize D4 with (g x).
        by rewrite <- H2 in D4. }
      { (* [pm1] is disjoint with [pm2] *)
      rewrite <- SAT2. auto. }

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D3 D4 D5 D6 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. generalize SAT1. intro SAT1'. apply pointsto_iter_conv_proc_std in SAT1.
    pose (ys := (map (expr_denot_map f1 s') xs) : list Loc).
    pose (ph1' := permheap_conv_std_mult ph1 ys).

    (* [ph2 l] is free for every [l] in the iterated separation conjunction *)
    assert (H3 : forall l, In l ys -> ph2 l = PHCfree). {
      intros l' H3. apply pointsto_iter_perm_full with (l := l') in SAT1; vauto.
      rewrite permheap_conv_std_mult_full in SAT1.
      unfold permheap_disj in D1. specialize D1 with l'.
      by apply phc_disj_full_free in D1. }

    (* [phJ l] is free for every [l] in the iterated separation conjunction *)
    assert (H4 : forall l, In l ys -> phJ l = PHCfree). {
      intros l' H4. apply pointsto_iter_perm_full with (l := l') in SAT1; vauto.
      rewrite permheap_conv_std_mult_full in SAT1.
      unfold permheap_disj in D3. specialize D3 with l'.
      apply phc_disj_full_free in D3; vauto.
      rewrite <- permheap_add_cell. rewrite H3; auto.
      by rewrite phc_add_iden_l. }

    (* [phF l] is free for every [l] in the iterated separation conjunction *)
    assert (H5 : forall l, In l ys -> phF l = PHCfree). {
      intros l' H5. apply pointsto_iter_perm_full with (l := l') in SAT1; vauto.
      rewrite permheap_conv_std_mult_full in SAT1.
      unfold permheap_disj in D4. specialize D4 with l'.
      apply phc_disj_full_free in D4; vauto.
      repeat rewrite <- permheap_add_cell.
      rewrite H3, H4; auto. by repeat  rewrite phc_add_iden_l. }

    exists (permheap_add ph1' ph2), phJ. repeat split; vauto.

    { (* disjointness of [ph1' + ph2] and [phJ] *)
    subst ph1'.
    rewrite <- permheap_conv_std_mult_free with ys ph2; auto.
    rewrite <- permheap_conv_std_mult_add; vauto.
    rewrite <- permheap_conv_std_mult_free with ys phJ; auto.
    by apply permheap_conv_std_mult_disj. }

    { (* disjointness of [ph1' + ph2 + phJ] and [phF] *)
    subst ph1'.
    rewrite <- permheap_conv_std_mult_free with ys ph2; auto.
    rewrite <- permheap_conv_std_mult_add; vauto.
    rewrite <- permheap_conv_std_mult_free with ys phJ; auto.
    rewrite <- permheap_conv_std_mult_add; vauto.
    rewrite <- permheap_conv_std_mult_free with ys phF; auto.
    by apply permheap_conv_std_mult_disj. }

    { (* the heap concretisation is proper *)
    subst ph1'.
    rewrite <- permheap_conv_std_mult_free with (xs := ys)(ph := ph2) at 1; auto.
    rewrite <- permheap_conv_std_mult_add; vauto.
    rewrite <- permheap_conv_std_mult_free with (xs := ys)(ph := phJ) at 1; auto.
    rewrite <- permheap_conv_std_mult_add; vauto.
    rewrite <- permheap_conv_std_mult_free with (xs := ys)(ph := phF) at 1; auto.
    rewrite <- permheap_conv_std_mult_add; vauto.
    by rewrite permheap_conv_std_mult_concr. }

    unfold assn_sat in SAT2. destruct SAT2 as (pmv & D7 & H6).
    assert (H8 : pmv = PMfree). { by apply pmv_disj_full_free in D7. }
    clarify. rewrite pmv_add_iden_l in H6.

    (* the map [pm1] is free at (g x) *)
    assert (H9 : pm1 (g x) = PMfree). {
      unfold procmap_disj in D2. specialize D2 with (g x).
      symmetry in D2. apply pmv_disj_full_free in D2; vauto.
      rewrite H6. vauto. }
    (* the entry [pm (g x)] equals [pm2 (g x)] *)
    assert (H10 : pmv_eq (pm (g x)) (pm2 (g x))). {
      unfold procmap_eq in H2. specialize H2 with (g x).
      rewrite <- H2. rewrite <- procmap_add_pmv.
      rewrite H9, H6. by rewrite pmv_add_iden_r. }
    rewrite H6 in H10.
    (* the map [pmJ] is free at (g x) *)
    assert (H11 : pmJ (g x) = PMfree). {
      unfold procmap_disj in D5. specialize D5 with (g x).
      apply pmv_disj_full_free in D5; vauto.
      rewrite H10. vauto. }
    (* the map [pmF] is free at (g x) *)
    assert (H12 : pmF (g x) = PMfree). {
      unfold procmap_disj in D6. specialize D6 with (g x).
      rewrite <- procmap_add_pmv in D6. rewrite H11 in D6.
      rewrite pmv_add_iden_l in D6. apply pmv_disj_full_free in D6; vauto.
      rewrite H10. vauto. }
    (* the map [pmC] is full at (g x) *)
    assert (H13 : pmv_full (pmC (g x))). {
      unfold procmap_eq in H1. specialize H1 with (g x).
      rewrite <- H1. repeat rewrite <- procmap_add_pmv.
      rewrite H10, H11, H12. repeat rewrite pmv_add_iden_l. vauto. }
    (* the new snapshot heap equals the old snapshot heap at all locations accessed by entries in [pmC] other than [pmC (g x)] *)
    assert (H14 : forall pid l, pid <> g x -> In l (pmv_acc (pmC pid)) ->
        permheap_snapshot (permheap_add (permheap_add (permheap_add ph1' ph2) phJ) phF) l =
        permheap_snapshot (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF) l). {
      intros pid l K1 K2. subst ph1'.
      assert (H : ~ In l ys). {
        intro K3. unfold procmap_ws in WS1. apply WS1 with (pid2 := g x) in K2; vauto.
        unfold procmap_eq in H1. specialize H1 with (g x).
        rewrite <- H1. repeat rewrite <- procmap_add_pmv.
        rewrite H10, H11, H12. repeat rewrite pmv_add_iden_l. vauto. }
      rewrite <- permheap_conv_std_mult_free with (xs := ys)(ph := ph2) at 1; auto.
      rewrite <- permheap_conv_std_mult_add; vauto.
      rewrite <- permheap_conv_std_mult_free with (xs := ys)(ph := phJ) at 1; auto.
      rewrite <- permheap_conv_std_mult_add; vauto.
      rewrite <- permheap_conv_std_mult_free with (xs := ys)(ph := phF) at 1; auto.
      rewrite <- permheap_conv_std_mult_add; vauto.
      unfold permheap_snapshot. by rewrite <- permheap_conv_std_mult_pres. }
    exists (update pm (g x) PMfree), pmJ, (update pmC (g x) PMfree).
    repeat split; vauto.
    { (* the updated [pm] is still disjoint with [pmJ] *)
    intro pid'. unfold update. desf.
    apply pmv_disj_iden_r. by apply procmap_disj_valid_r in D5. }
    { (* the updated [pm + pmJ] is still disjoint with [pmJ] *)
    intro pid'. rewrite <- procmap_add_pmv. unfold update. desf.
    - rewrite pmv_add_iden_r.
      apply pmv_disj_add_l with (pm (g x)); vauto. apply D6.
    - by apply D6. }
    { (* the update [pm + pmJ + pmF] equals the updated [pmC] *)
    intro pid'. repeat rewrite <- procmap_add_pmv.
    unfold update. desf.
    - rewrite H11, H12. by rewrite pmv_add_iden_r.
    - by apply H1. }
    { (* the new process map is finite *)
    by apply procmap_finite_upd. }
    { (* the new process map is well-structured *)
    apply procmap_ws_upd; vauto. }
    { (* the new process map covers the new snapshot heap *)
    red. intro pid. unfold update. desf.
    apply pmv_covers_agrees with (permheap_snapshot (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF)); vauto.
    intros l K1. rewrite H14 with (pid := pid); intuition vauto. }
    { (* the new process map is safe with the new snapshot heap *)
    red. intro pid. unfold update. desf.
    apply pmv_safe_heap_acc with (permheap_snapshot (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF)); vauto.
    intros l K1. rewrite H14 with (pid := pid); intuition vauto. }
    exists g, Cskip. repeat split; vauto.
    { (* the ghost semantics can make a matching step *)
    apply pmv_full_content in H13.

    destruct H13 as (p' & P' & xs' & f & H13). clarify.
    unfold procmap_eq in H1. specialize H1 with (g x).
    rewrite H13 in H1. repeat rewrite <- procmap_add_pmv in H1.
    rewrite H10, H11, H12 in H1. repeat rewrite pmv_add_iden_l in H1.
    simpl in H1. desf.
    apply gsos_proc_end with p' P' xs' f; vauto.
    + by rewrite H13.
    + inv H7. destruct H as (K1 & K2 & K3 & K4).
      apply K3. vauto. }

    apply safe_done.
    exists ph1', ph2. repeat split.

    { (* [ph1'] is disjoint with [ph2] *)
    subst ph1'. rewrite <- permheap_conv_std_mult_free with ys ph2; auto.
    by apply permheap_conv_std_mult_disj. }

    exists pm1, (update pm2 (g x) PMfree). repeat split; vauto.

    { (* [pm1] is disjoint with the updated map [pm2'] *)
    intro pid'. unfold update. desf.
    apply pmv_disj_iden_l. unfold procmap_disj in D2.
    specialize D2 with (g x). by apply pmv_disj_valid_l in D2. }

    { (* [pm1 + pm2'] equals the update map [pm] *)
    intro pid'. rewrite <- procmap_add_pmv. unfold update. desf.
    + rewrite pmv_add_iden_l. by rewrite H9.
    + by apply H2. }

    unfold procmap_safe in PSAFE1. specialize PSAFE1 with (g x).
    unfold procmap_eq in H1. specialize H1 with (g x).
    rewrite <- H1 in PSAFE1. repeat rewrite <- procmap_add_pmv in PSAFE1.
    rewrite H10, H11, H12 in PSAFE1. repeat rewrite pmv_add_iden_l in PSAFE1.
    simpl in PSAFE1.

    (* fix a process store [ps] and show that [ps] is valid with [Pepsilon] and the postcondition of [p] *)
    set (ps := expr_denot_map f2 s' : ProcStore).
    assert (CSV1 : forall y : ProcVar, In y xs -> ph1 (F1 y) = PHCproc perm_full (F2 y)). {
      intros y CSV1.
      apply pointsto_iter_sat_single_proc with (x0 := y) in SAT1'; auto.
      apply phc_le_full_eq in SAT1'; vauto.
      by apply permheap_disj_valid_l in D1. }
    assert (CSV2 : forall y : ProcVar, In y xs -> phc_snapshot (ph1 (F1 y)) = Some (F2 y)). {
      intros y CSV2. rewrite CSV1; auto. }
    assert (CSV3 : forall y : ProcVar, In y xs -> 
        phc_snapshot (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF (F1 y)) =
        phc_snapshot (ph1 (F1 y))). {
      intros y CSV3. rewrite CSV2; auto.
      repeat apply phc_snapshot_add; auto. }
    assert (CSV4 : forall y : ProcVar, In y xs ->
        phc_snapshot (permheap_add (permheap_add (permheap_add ph1 ph2) phJ) phF (F1 y)) = Some (ps y)). {
      intros y IN1. rewrite CSV3; auto. }
    assert (CSV5 : proc_valid (snd (env p)) P ps). {
      apply PSAFE1. intros y IN1. apply CSV4; auto. }

    unfold assn_sat. rewrite bexpr_denot_conv with (ps := ps); vauto.
    subst b2. inv CSV5. destruct H as (K3 & K4). apply K3. vauto.
Qed.


(** *** Action rule *)

Lemma phc_concr_snapshot_none :
  forall pmv,
  phc_concr pmv = None ->
  phc_snapshot pmv = None.
Proof.
  intros pmv H1. unfold phc_concr, phc_snapshot in *.
  desf.
Qed.

(* ------- *)

Definition metadata_agree (pid : ProcID)(p : ProcLabel)(a : ActLabel)(xs : list ProcVar)(f : ProcVar -> Loc)(h hs : Heap)(pm : ProcMap) : Prop :=
  (* (1) the process map [pm] must have an entry at [pid] *)
  exists (q : Qc)(P : Proc),
    pmv_eq (pm pid) (PMelem q p P xs f) /\
  (* (2) all free variables of the action [a] must be covered by [pm pid] *)
    (forall x : ProcVar, In x (act_fv a) -> In x xs) /\
  (* (3) the heaps [h] and [hs] must agree on all heap locations corresponding to variables in [xs] *)
    (forall x : ProcVar, In x xs -> h (f x) = hs (f x)) /\
  (* (4) a process store can be constructed from the heap that satisfies the guard of [a] *)
    exists ps : ProcStore,
      (forall x : ProcVar, In x xs -> h (f x) = Some (ps x)) /\
        pbexpr_denot (guard a) ps = true.

Lemma metadata_agree_procmap_eq :
  forall pid p a xs f h hs pm1 pm2,
  procmap_eq pm1 pm2 ->
  metadata_agree pid p a xs f h hs pm1 ->
  metadata_agree pid p a xs f h hs pm2.
Proof.
  intros pid p a xs f h hs pm1 pm2 H1 H2.
  unfold metadata_agree in *.
  destruct H2 as (q & P & H2 & H3 & H4 & ps & H5 & H6).
  exists q, P. intuition vauto.
  rewrite <- H2. unfold procmap_eq in H1. auto.
Qed.

Add Parametric Morphism : metadata_agree
  with signature eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> procmap_eq ==> iff
    as metadata_agree_procmap_eq_mor.
Proof.
  intros pid p a xs f h hs pm1 pm2 H1. split; intro H2.
  - apply metadata_agree_procmap_eq with pm1; auto.
  - apply metadata_agree_procmap_eq with pm2; auto.
Qed.

Lemma metadata_agree_F :
  forall pid p a xs F1 F2 h hs pm,
    (forall x : ProcVar, In x xs -> F1 x = F2 x) ->
  metadata_agree pid p a xs F1 h hs pm ->
  metadata_agree pid p a xs F2 h hs pm.
Proof.
  intros pid p a xs F1 F2 h hs pm IN1 H1.
  unfold metadata_agree in *.
  destruct H1 as (q & P & H1 & H2 & H3 & ps & H4 & H5).
  exists q, P. intuition vauto.
  - rewrite H1. by apply pmv_eq_F.
  - rewrite <- IN1; vauto. by apply H3.
  - exists ps. split; vauto. intros y IN2.
    rewrite <- IN1; auto.
Qed.

Lemma safe_action (env : ProcEnv) :
  forall n C ph pm pm' s g x hs q p P Q (xs ys1 ys2 : list ProcVar) a (fq : ProcVar -> Qc)(f1 f2 : ProcVar -> Expr)(J A : Assn),
  let B2 := pbexpr_convert (effect a) f2 in
  let F1 := expr_denot_map f1 s : ProcVar -> Loc in
  metadata_agree (g x) p a xs F1 hs (permheap_snapshot ph) pm' ->
  Permutation xs (ys1 ++ ys2) ->
  (forall y : ProcVar, In y ys1 -> fq y <> perm_full) ->
  (forall y : ProcVar, In y ys2 -> fq y = perm_full) ->
  (forall y : ProcVar, In y xs -> perm_valid (fq y)) ->
  (forall y : ProcVar, disjoint (expr_fv (f1 y)) (cmd_mod C)) ->
  ~ cmd_mod C x ->
  cmd_basic C ->
  procmap_disj pm pm' ->
  assn_sat permheap_iden pm' s g (Aproc x q p (Palt (Pseq (Pact a) P) Q) xs f1) ->
  safe n env True C ph pm s g J (Astar (Astar (Aiter (pointsto_iter_procact xs fq f1 f2)) (Aplain B2)) A) ->
  safe n env False (Cinact (g x, a, hs) C) ph (procmap_add pm pm') s g J (Astar (Astar (Astar (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) (Aproc x q p P xs f1)) (Aplain B2)) A).
Proof.
  induction n as [|n IH]. vauto.
  intros C ph pm pm' s g x hs q p P Q xs ys1 ys2 a fq f1 f2 J A B2 F1 AGR1 PERM1 PERM2 PERM3 VF DISJ1 DISJ2 BASIC1 D1 SAT1 SAFE1.
  set (F2 := expr_denot_map f2 s : ProcVar -> Val).

  (* variable [y] is in [xs] iff [y] is in either [ys1] or [ys2] *)
  assert (PERM4 : forall y : ProcVar, In y xs <-> In y ys1 \/ In y ys2). {
    intro y. split; intros.
    - apply Permutation_in with (x := y) in PERM1; auto.
      apply in_app_or in PERM1.
      destruct PERM1 as [PERM1 | PERM1]; vauto.
    - symmetry in PERM1.
      apply Permutation_in with (x := y) in PERM1; auto.
      by apply in_or_app. }

  repeat split; vauto.

  (* (2) absence of faults - five possible faulting cases *)
  - red. clear IH. intros phF pmF D3 D4 FIN1 FIN2 ABORT1.
    destruct SAFE1 as (TERM1 & ABORT2 & _).
    inv ABORT1; vauto.

    (* case 1: fault in program [C] *)
    + rewrite procmap_add_assoc in H4.
      apply ABORT2 in H4; vauto.
      * by apply procmap_disj_assoc_l.
      * by rewrite <- procmap_add_assoc.

    (* case 2: the process map does not contain an entry at [pid] *)
    + apply H4. clear H4.
      destruct AGR1 as (q' & P' & AGR1 & _).
      assert (OCC1 : pmv_occ (pm' (g x))). { rewrite AGR1. vauto. }
      apply pmv_occ_add_l with (pmv2 := pm (g x)) in OCC1; auto.
      rewrite pmv_add_comm in OCC1.
      apply pmv_occ_add_l with (pmv2 := pmF (g x)) in OCC1; auto.
      by apply D4.

    (* case 3: not all process variables in [xs] are covered by the snapshot heap *)
    + unfold metadata_agree in AGR1.
      destruct AGR1 as (q' & P' & AGR1 & _ & _ & ps & AGR2 & _).
      repeat rewrite <- procmap_add_pmv in H5.
      destruct H8 as (x' & H8 & H9).
      assert (PAGR1 : pmv_occ (pm' (g x))). { rewrite AGR1. vauto. }
      assert (PAGR2 : pmv_weak_agree (pm' (g x)) (procmap_add pm pm' (g x))). {
        unfold procmap_add. rewrite pmv_add_comm.
        apply pmv_weak_agree_add_occ; auto. }
      assert (PAGR3 : pmv_weak_agree (pm' (g x)) (procmap_add (procmap_add pm pm') pmF (g x))). {
        transitivity (procmap_add pm pm' (g x)); auto.
        apply pmv_weak_agree_add_occ; auto.
        apply pmv_occ_add_r; auto. }
      rewrite AGR1 in PAGR3. repeat rewrite <- procmap_add_pmv in PAGR3.
      rewrite H5 in PAGR3. unfold pmv_weak_agree in PAGR3.
      repeat desf. rename xs0 into xs, p0 into p.
      assert (PC1 : forall y : ProcVar, In y xs -> f y = F1 y). {
        intros. apply map_eq_In with xs; vauto. }
      rewrite PC1 in H9; auto.
      rewrite AGR2 in H9; auto. by congruence.

    (* case 4: not all process variables in [xs] are covered by the concrete heap *)
    + destruct H8 as (x' & H8 & H9).
      destruct AGR1 as (q' & P' & AGR1 & AGR2 & AGR3 & ps & AGR4 & AGR5).
      assert (PAGR1 : pmv_occ (pm' (g x))). { rewrite AGR1. vauto. }
      assert (PAGR2 : pmv_weak_agree (pm' (g x)) (procmap_add pm pm' (g x))). {
        unfold procmap_add. rewrite pmv_add_comm.
        apply pmv_weak_agree_add_occ; auto. }
      assert (PAGR3 : pmv_weak_agree (pm' (g x)) (procmap_add (procmap_add pm pm') pmF (g x))). {
        transitivity (procmap_add pm pm' (g x)); auto.
        apply pmv_weak_agree_add_occ; auto.
        apply pmv_occ_add_r; auto. }
      rewrite AGR1 in PAGR3. repeat rewrite <- procmap_add_pmv in PAGR3.
      rewrite H5 in PAGR3. unfold pmv_weak_agree in PAGR3.
      repeat desf. rename xs0 into xs, p0 into p.
      rename q0 into q'', P0 into P''.
      assert (PC1 : forall y : ProcVar, In y xs -> f y = F1 y). {
        intros. apply map_eq_In with xs; vauto. }
      assert (K1 : phc_concr (ph (f x')) = None). {
        apply phc_concr_le_none with (phc_add (ph (f x')) (phF (f x'))); vauto.
        apply phc_le_mono_pos; auto. }
      assert (K2 : phc_snapshot (ph (f x')) = None). {
        by apply phc_concr_snapshot_none. }
      assert (K3 : hs (F1 x') = None). {
        rewrite AGR3; auto. unfold permheap_snapshot.
        rewrite <- K2; vauto. rewrite PC1; vauto. }
      assert (K4 : hs (F1 x') = Some (ps x')). { by apply AGR4. }
      by congruence.

    (* case 5: the process semantics can not make a synchronising step *)
    + assert (SAT2 : @Cskip GhostMetadata = Cskip). { vauto. }
      apply TERM1 in SAT2. clear TERM1.

      (* TODO description *)
      assert (V1 : permheap_valid ph). { by apply permheap_disj_valid_l in D3. }
      assert (V2 : procmap_valid pm). { by apply procmap_disj_valid_l in D1. }

      apply assn_weaken_l in SAT2; auto.
      destruct SAT2 as (ph1 & ph2 & D5 & H13 & pm1 & pm2 & D6 & H14 & SAT2 & SAT3).
      destruct AGR1 as (q' & P' & AGR1 & AGR2 & AGR3 & ps & AGR4 & AGR5).
      destruct SAT1 as (pmv & D7 & SAT1).

      (* TODO description  *)
      assert (PAGR1 : pmv_occ (pm' (g x))). { rewrite AGR1. vauto. }
      assert (PAGR2 : pmv_weak_agree (pm' (g x)) (procmap_add pm pm' (g x))). {
        unfold procmap_add. rewrite pmv_add_comm.
        apply pmv_weak_agree_add_occ; auto. }
      assert (PAGR3 : pmv_weak_agree (pm' (g x)) (procmap_add (procmap_add pm pm') pmF (g x))). {
        transitivity (procmap_add pm pm' (g x)); auto.
        apply pmv_weak_agree_add_occ; auto.
        apply pmv_occ_add_r; auto. }

      rewrite AGR1 in PAGR3. repeat rewrite <- procmap_add_pmv in PAGR3.
      rewrite H7 in PAGR3. unfold pmv_weak_agree in PAGR3.
      repeat desf.
      rename q0 into q'', p0 into p', P0 into P'', xs0 into xs.

      (* TODO description *)
      assert (K1 : forall y : ProcVar, In y xs -> f y = F1 y). {
        intros. by apply map_eq_In with xs. }
      assert (K2 : pstore_agree xs ps ps1). {
        intros y K2.
        cut (Some (ps y) = Some (ps1 y)); [intuition vauto|].
        rewrite <- AGR4, <- H8; vauto. rewrite K1; vauto. }
      assert (K3 : pbexpr_denot (guard a) ps1 = true). {
        rewrite pbexpr_agree with (ps2 := ps); vauto.
        apply pstore_agree_weaken with xs; [|by symmetry].
        intros y K3. apply AGR2. unfold act_fv.
        apply in_or_app. by left. }
      assert (K4 : forall y : ProcVar, In y (pbexpr_fv (effect a)) -> In y xs). {
        intros y K4. apply AGR2. unfold act_fv.
        apply in_or_app. by right. }
      assert (V3 : permheap_valid ph1). { by apply permheap_disj_valid_l in D5. }
      assert (V4 : procmap_valid pm1). { by apply procmap_disj_valid_l in D6. }

      apply assn_sat_procact_iter_permut with (ys := ys1 ++ ys2) in SAT2; auto.
      apply pointsto_iter_procact_split in SAT2; auto.
      destruct SAT2 as (ph1a & ph1b & D8 & ADD1 & pm1a & pm1b & D9 & ADD2 & SAT1a & SAT1b).
      clarify.

      (* TODO description *)
      assert (HC1 : forall y : ProcVar, In y ys1 ->
          exists q : Qc, perm_valid q /\ ph1a (expr_denot (f1 y) s) = PHCproc q (expr_denot (f2 y) s)). {
        intros y HC1.
        apply pointsto_iter_sat_single_proc with (x0 := y) in SAT1a; auto.
        apply phc_le_diff in SAT1a; vauto.
        - destruct SAT1a as (phc & D11 & SAT1a). rewrite <- SAT1a.
          unfold phc_disj in D11. destruct phc as [|q'''|q'''|q'''|]; vauto.
          unfold phc_add. desf. exists (fq y + q'''); split; vauto.
          by apply perm_add_valid.
        - simpl. apply VF. rewrite PERM4. by left.
        - by apply permheap_disj_valid_l in D8. }
      assert (HC2 : forall y : ProcVar, In y ys2 ->
          exists v : Val, ph1b (expr_denot (f1 y) s) = PHCact perm_full (expr_denot (f2 y) s) v). {
        intros y HC2.
        apply pointsto_iter_sat_single_act with (x0 := y) in SAT1b; auto.
        destruct SAT1b as (v & SAT1b).
        apply phc_le_full_eq in SAT1b; vauto.
        - rewrite <- SAT1b. exists v. rewrite PERM3; vauto.
        - by apply permheap_disj_valid_r in D8.
        - rewrite PERM3; vauto. }

      (* the effect of [a] holds with [ps2] *)
      assert (K5 : pbexpr_denot (effect a) ps2 = true). {
        rewrite <- bexpr_denot_conv with (s := s)(f := f2); vauto.
        intros y K5.
        cut (Some (ps2 y) = Some (expr_denot (f2 y) s)); [intuition vauto|].
        rewrite <- H9; [|by apply K4].
        rewrite K1; [|by apply K4].
        apply K4 in K5. rewrite PERM4 in K5. destruct K5 as [K5 | K5].
        - apply HC1 in K5. destruct K5 as (q''' & K5 & K6).
          unfold permheap_concr.
          repeat (rewrite <- permheap_add_cell; apply phc_concr_add; auto).
          subst F1. unfold expr_denot_map. rewrite K6. simpls.
        - apply HC2 in K5. destruct K5 as (v & K5).
          unfold permheap_concr.
          rewrite <- permheap_add_cell. apply phc_concr_add; auto.
          rewrite <- permheap_add_cell. apply phc_concr_add; auto.
          rewrite permheap_add_comm.
          rewrite <- permheap_add_cell. apply phc_concr_add; auto.
          subst F1. unfold expr_denot_map.
          rewrite K5. simpls. }

      (* determine the contents of [pm' (g x)] *)
      rewrite AGR1 in SAT1. apply pmv_eq_equality in AGR1.
      destruct AGR1 as (Q' & F1' & AGR1 & PEQ1).
      rewrite PEQ1 in SAT1. clear PEQ1.

      (* the process component in [pm + pm' + pmF (g x)] is able to do an [a] step  *)
      assert (PC1 : exists q1 Q1, pmv_eq (PMelem q' p' Q' xs F1') (PMelem q1 p' (Ppar (Palt (Pseq (Pact a) P) Q) Q1) xs F1')). {
        red in D7. unfold pmv_add in SAT1. repeat desf.
        - exists (q + q0), P0. rewrite SAT1. vauto. red in SAT1. desf.
        - exists q, Pepsilon. rewrite proc_M1, proc_M4. red in SAT1. desf. }
      destruct PC1 as (q1 & Q1 & PC1).
      assert (PC2 : exists q2 Q2, pmv_eq (pmv_add (pm (g x)) (PMelem q' p' Q' xs F1')) (PMelem q2 p' (Ppar Q' Q2) xs F1') ). {
        red in D1. specialize D1 with (g x). rewrite AGR1 in D1. red in D1.
        unfold pmv_add. repeat desf; vauto.
        - exists (q0 + q'), P0. by rewrite proc_M1.
        - exists q', Pepsilon. by rewrite proc_M1, proc_M4. }
      destruct PC2 as (q2 & Q2 & PC2).
      rewrite <- AGR1 in PC2.
      assert (PC3 : exists q3 Q3, pmv_eq (pmv_add (PMelem q2 p' (Ppar Q' Q2) xs F1') (pmF (g x))) (PMelem q3 p' (Ppar Q' Q3) xs F1')). {
        red in D4. specialize D4 with (g x). rewrite PC2 in D4. red in D4.
        unfold pmv_add. repeat desf; vauto.
        exists (q2 + q0), (Ppar Q2 P0). by rewrite proc_M2. }
      destruct PC3 as (q3 & Q3 & PC3).
      rewrite <- PC2 in PC3. clear PC2 q2 Q2.
      repeat rewrite procmap_add_pmv in PC3.
      rewrite H7 in PC3.

      (* the process [P''] can do an [a] step and end up in some process [P'''] *)
      assert (PS1 : proc_bisim Q' (Ppar (Palt (Pseq (Pact a) P) Q) Q1)). {
        red in PC1. repeat desf. }
      assert (PS2 : proc_sos (Ppar (Palt (Pseq (Pact a) P) Q) Q1) ps1 a (Ppar (Pseq Pepsilon P) Q1) ps2). {
        apply pstep_par_l, pstep_alt_l, pstep_seq_l, pstep_act; auto. }
      assert (PS3 : exists Q'', proc_sos Q' ps1 a Q'' ps2). {
        inv PS1. destruct H as (_ & H & _).
        apply H in PS2. destruct PS2 as (Q'' & PS2 & PS3). by exists Q''. }
      destruct PS3 as (Q'' & PS3).
      assert (PS4 : proc_sos (Ppar Q' Q3) ps1 a (Ppar Q'' Q3) ps2). {
        by apply pstep_par_l. }
      assert (PS5 : proc_bisim P'' (Ppar Q' Q3)). {
        red in PC3. repeat desf. }
      assert (PS6 : exists P''', proc_sos P'' ps1 a P''' ps2). {
        inv PS5. destruct H as (_ & H & _).
        apply H in PS4. destruct PS4 as (P''' & PS4 & _).
        by exists P'''. }
      destruct PS6 as (P''' & PS6).

      (* the proof concludes by contradiction of H10 and PS6 *)
      apply H10. by exists P'''.

  (* (3) all shared-memory accesses are in the footprint *)
  - intros l H1. simpl in H1.
    destruct SAFE1 as (_ & _ & ACC & _).
    by apply ACC.

  (* (4) all shared-memory writes are in the footprint *)
  - intros l H1. simpl in H1.
    destruct SAFE1 as (_ & _ & _ & WRITES & _).
    by apply WRITES.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D2 D3 D4 D5 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP.

    (* the program [C] is empty *)
    + assert (C = Cskip). { by apply plain_skip. }
      clarify. clear IH. destruct SAFE1 as (SAFE1' & _).
      assert (SAFE1 : Cskip = @Cskip GhostMetadata). { trivial. }
      apply SAFE1' in SAFE1. clear SAFE1'.
      destruct SAFE1 as (ph3' & ph3 & D6 & H2 & pm3' & pm3 & D7 & H4 & SAT2 & SAT3).
      destruct SAT2 as (ph2' & ph2 & D8 & H5 & pm2' & pm2 & D9 & H6 & SAT2 & SAT4).
      clarify.

      (* [ph2'] and [pm2'] are both valid *)
      assert (V1 : permheap_valid ph2'). { by apply permheap_disj_valid_l in D8. }
      assert (V2 : procmap_valid pm2'). { by apply procmap_disj_valid_l in D9. }

      (* splitting the iterated separating conjunction in SAT2 *)
      apply assn_sat_procact_iter_permut with (ys := ys1 ++ ys2) in SAT2; auto.
      apply pointsto_iter_procact_split in SAT2; auto.
      destruct SAT2 as (ph1a & ph1b & D10 & H7 & pm1a & pm1b & D11 & H8 & SAT1a & SAT1b). clarify.
      set (ls := map (expr_denot_map f1 s') xs : list Loc).
      set (ls1 := map (expr_denot_map f1 s') ys1 : list Loc).
      set (ls2 := map (expr_denot_map f1 s') ys2 : list Loc).
      set (ph1b' := permheap_conv_proc_mult ph1b ls2).

      (* [ph1a], [ph1b], [pm1a] and [pm1b] are all valid *)
      assert (V3 : permheap_valid ph1a). { by apply permheap_disj_valid_l in D10. }
      assert (V4 : permheap_valid ph1b). { by apply permheap_disj_valid_r in D10. }
      assert (V5 : procmap_valid pm1a). { by apply procmap_disj_valid_l in D11. }
      assert (V6 : procmap_valid pm1b). { by apply procmap_disj_valid_r in D11. }

      (* [ph1a l] contains a process cell for every [l] in [ls1], and [ph1b l] contains a full action cell for every [l] in [ls2] *)
      assert (HV1 : forall y : ProcVar, In y ys2 -> exists v : Val, ph1b (F1 y) = PHCact perm_full (F2 y) v). {
        intros y HV1. apply pointsto_iter_sat_single_act with (x0 := y) in SAT1b; auto.
        destruct SAT1b as (v & SAT1b). rewrite PERM3 in SAT1b; auto.
        apply phc_le_full_eq in SAT1b; vauto. subst F1.
        unfold expr_denot_map. rewrite <- SAT1b. by exists v. }
      assert (HV1' : forall l : Loc, In l ls2 -> exists v1 v2 : Val, ph1b l = PHCact perm_full v1 v2). {
        intros l HV1'. subst ls2. apply in_map_iff in HV1'.
        destruct HV1' as (y & ? & HV1').
        apply HV1 in HV1'. destruct HV1' as (v & HV1').
        clarify. by exists (expr_denot (f2 y) s'), v. }
      assert (HV2 : forall y : ProcVar, In y ys1 -> exists q : Qc, perm_valid q /\ ph1a (F1 y) = PHCproc q (F2 y)). {
        intros y HV2. apply pointsto_iter_sat_single_proc with (x0 := y) in SAT1a; auto.
        apply phc_le_diff in SAT1a; vauto.
        - destruct SAT1a as (phc & D12 & SAT1a). subst F1.
          unfold expr_denot_map. rewrite <- SAT1a.
          red in D12. destruct phc as [|q''|q''|q''|]; vauto.
          unfold phc_add. desf. exists (fq y + q''); split; vauto.
          by apply perm_add_valid.
        - simpl. apply VF. rewrite PERM4. by left. }
      assert (HV2' : forall l : Loc, In l ls1 -> exists q v, perm_valid q /\ ph1a l = PHCproc q v). {
        intros l HV2'. subst ls1. apply in_map_iff in HV2'.
        destruct HV2' as (y & ? & HV2').
        apply HV2 in HV2'. destruct HV2' as (q' & ? & HV2').
        clarify. exists q', (expr_denot (f2 y) s'). split; vauto. }
      assert (HV3 : forall y : ProcVar, In y ys1 -> ph1b (F1 y) = PHCfree \/ exists q v, perm_valid q /\ ph1b (F1 y) = PHCproc q v). {
        intros y HV3. apply HV2 in HV3. destruct HV3 as (? & ? & HV3).
        red in D10. specialize D10 with (F1 y).
        rewrite HV3 in D10. red in D10. repeat desf; vauto.
        right. exists q0, (expr_denot (f2 y) s'). intuition vauto.
        by apply perm_disj_valid_r in D10. }

      (* [ph1b l] is full, and [ph1a l], [ph2 l], [ph3 l], [phJ l] and [phF l] are all empty for every [l] in [ls2] *)
      assert (HC1 : forall l : Loc, In l ls2 -> phc_full (ph1b l)). {
        intros l HC1. apply HV1' in HC1. destruct HC1 as (? & ? & HC1). rewrite HC1. simpls. }
      assert (HC2 : forall l : Loc, In l ls2 -> ph1a l = PHCfree). {
        intros l HC2. red in D10. specialize D10 with l. symmetry in D10.
        apply phc_disj_full_free in D10; auto. }
      assert (HV4 : forall y : ProcVar, In y ys2 -> ph1a (F1 y) = PHCfree). {
        intros y HC2'. apply HC2. subst ls2. by apply in_map. }
      assert (HC3 : forall l : Loc, In l ls2 -> ph2 l = PHCfree). {
        intros l HC3. red in D8. specialize D8 with l. rewrite <- permheap_add_cell in D8.
        rewrite HC2 in D8; auto. rewrite phc_add_iden_r in D8.
        apply phc_disj_full_free in D8; auto. }
      assert (HC4 : forall l : Loc, In l ls2 -> ph3 l = PHCfree). {
        intros l HC4. red in D6. specialize D6 with l.
        apply phc_disj_full_free in D6; auto.
        repeat rewrite <- permheap_add_cell. rewrite HC2, HC3; auto.
        rewrite phc_add_iden_l, phc_add_iden_r. by apply HC1. }
      assert (HC5 : forall l : Loc, In l ls2 -> phJ l = PHCfree). {
        intros l HC5. red in D2. specialize D2 with l.
        apply phc_disj_full_free in D2; auto.
        repeat rewrite <- permheap_add_cell. rewrite HC2, HC3, HC4; auto.
        rewrite phc_add_iden_l, phc_add_iden_r, phc_add_iden_l. by apply HC1. }
      assert (HC6 : forall l : Loc, In l ls2 -> phF l = PHCfree). {
        intros l HC6. red in D3. specialize D3 with l.
        apply phc_disj_full_free in D3; auto.
        repeat rewrite <- permheap_add_cell. rewrite HC2, HC3, HC4, HC5; auto.
        repeat rewrite phc_add_iden_l. rewrite phc_add_iden_r. by apply HC1. }

      (* the heap [ph1b'] is disjoint in every compositions in which [ph1b] is also disjoint *)
      assert (DISJ3 : permheap_disj ph1a ph1b'). {
        rewrite <- permheap_conv_proc_mult_free with ls2 ph1a; auto.
        by apply permheap_conv_proc_mult_disj. }
      assert (DISJ4 : permheap_disj (permheap_add ph1a ph1b') ph2). {
        rewrite <- permheap_conv_proc_mult_free with ls2 ph1a; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 ph2; auto.
        subst ph1b'. rewrite <- permheap_conv_proc_mult_add; vauto.
        by apply permheap_conv_proc_mult_disj. }
      assert (DISJ5 : permheap_disj (permheap_add (permheap_add ph1a ph1b') ph2) ph3). {
        rewrite <- permheap_conv_proc_mult_free with ls2 ph1a; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 ph2; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 ph3; auto.
        subst ph1b'. repeat rewrite <- permheap_conv_proc_mult_add; vauto.
        by apply permheap_conv_proc_mult_disj. }
      assert (DISJ6 : permheap_disj (permheap_add (permheap_add (permheap_add ph1a ph1b') ph2) ph3) phJ). {
        rewrite <- permheap_conv_proc_mult_free with ls2 ph1a; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 ph2; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 ph3; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 phJ; auto.
        subst ph1b'. repeat rewrite <- permheap_conv_proc_mult_add; vauto.
        by apply permheap_conv_proc_mult_disj. }
      assert (DISJ7 : permheap_disj (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b') ph2) ph3) phJ) phF). {
        rewrite <- permheap_conv_proc_mult_free with ls2 ph1a; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 ph2; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 ph3; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 phJ; auto.
        rewrite <- permheap_conv_proc_mult_free with ls2 phF; auto.
        subst ph1b'. repeat rewrite <- permheap_conv_proc_mult_add; vauto.
        by apply permheap_conv_proc_mult_disj. }

      (* the heap location [l] is in [ls] iff [l] is in [ls1] or [ls2] *)
      assert (LDISJ1 : forall l : Loc, In l ls <-> In l ls1 \/ In l ls2). {
        intro l. split; intro LDISJ.
        - subst ls. apply in_map_iff in LDISJ.
          destruct LDISJ as (y & LDISJ1 & LDISJ2). clarify.
          apply PERM4 in LDISJ2. destruct LDISJ2 as [LDISJ2 | LDISJ2].
          + left. subst ls1. by apply in_map.
          + right. subst ls2. by apply in_map.
        - destruct LDISJ as [LDISJ | LDISJ].
          + subst ls1. apply in_map_iff in LDISJ.
            destruct LDISJ as (y & LDISJ1 & LDISJ2). clarify.
            subst ls. apply in_map, PERM4. by left.
          + subst ls2. apply in_map_iff in LDISJ.
            destruct LDISJ as (y & LDISJ1 & LDISJ2). clarify.
            subst ls. apply in_map, PERM4. by right. }

      (* the lists [ls1] and [ls2] are disjoint, as well as [xs1] and [xs2] *)
      assert (LDISJ2 : forall l : Loc, In l ls1 -> In l ls2 -> False). {
        intros l IN1 IN2.
        apply HV1' in IN2. destruct IN2 as (? & ? & IN2).
        apply HV2' in IN1. destruct IN1 as (q' & ? & V7 & IN1).
        red in D10. specialize D10 with l.
        rewrite IN1, IN2 in D10. red in D10. repeat desf. }
      assert (LDISJ3 : forall y : ProcVar, In y ys1 -> In y ys2 -> False). {
        intros y IN1 IN2. apply LDISJ2 with (expr_denot_map f1 s' y).
        - subst ls1. by apply in_map.
        - subst ls2. by apply in_map. }
      assert (LDISJ4 : forall l : Loc, In l ls1 -> In l ls). {
        intros l LDISJ4. rewrite LDISJ1. by left. }
      assert (LDISJ5 : forall l : Loc, In l ls2 -> In l ls). {
        intros l LDISJ5. rewrite LDISJ1. by right. }

      exists (permheap_add (permheap_add (permheap_add ph1a ph1b') ph2) ph3), phJ.
      repeat split; vauto.

      { (* all concrete heap values are preserved by the computation step *)
      rewrite <- permheap_conv_proc_mult_free with (xs := ls2)(ph := ph1a) at 1; auto.
      rewrite <- permheap_conv_proc_mult_free with (xs := ls2)(ph := ph2) at 1; auto.
      rewrite <- permheap_conv_proc_mult_free with (xs := ls2)(ph := ph3) at 1; auto.
      rewrite <- permheap_conv_proc_mult_free with (xs := ls2)(ph := phJ) at 1; auto.
      rewrite <- permheap_conv_proc_mult_free with (xs := ls2)(ph := phF) at 1; auto.
      subst ph1b'. repeat rewrite <- permheap_conv_proc_mult_add; vauto.
      by apply permheap_conv_proc_mult_concr. }

      (* determine the exact contents of [pm' (g x)] *)
      destruct SAT1 as (pmv & D12 & SAT1).
      destruct AGR1 as (q' & P' & AGR1 & AGR2 & AGR3 & ps1 & AGR4 & AGR5).
      rewrite AGR1 in SAT1. apply pmv_eq_equality in AGR1.
      destruct AGR1 as (P'' & F1' & AGR1 & PEQ1).
      rewrite PEQ1 in SAT1. clear PEQ1.
      clear P'. rename P'' into P'.

      (* getting rid of [pmv] *)
      assert (PMV1 : exists R : Proc,
          (pmv = PMfree /\ R = Pepsilon /\ q = q') \/
          (exists q'', pmv_eq pmv (PMelem q'' p R xs F1) /\ perm_disj q q'' /\ q' = q + q'')). {
        red in D12. repeat desf; vauto.
        - exists P0. right. exists q0. red in SAT1.
          unfold pmv_add in SAT1. repeat desf.
        - exists Pepsilon. left. repeat split; vauto.
          rewrite pmv_add_iden_l in SAT1.
          red in SAT1. repeat desf. }
      destruct PMV1 as (R & PMV1).

      (* TODO description *)
      assert (PACC1 : map F1' xs = ls). {
        destruct PMV1 as [(PMV1 & PMV2 & PMV3) | (q'' & PMV1 & PMV2 & PMV3)]; vauto.
        - rewrite pmv_add_iden_l in SAT1.
          unfold pmv_eq in SAT1. subst ls. repeat desf.
        - rewrite PMV1 in SAT1. unfold pmv_add in SAT1. repeat desf.
          unfold pmv_eq in SAT1. subst ls. repeat desf. }
      assert (PACC2 : pmv_acc (pm' (g x)) = ls). { by rewrite AGR1. }
      assert (PACC3 : forall l : Loc, In l ls -> In l (pmv_acc (pmC (g x)))). {
        intros l PACC3. red in H1. specialize H1 with (g x).
        rewrite <- H1. rewrite <- PACC2 in PACC3.
        apply pmv_acc_add, pmv_acc_add; auto.
        rewrite <- procmap_add_pmv, pmv_add_comm.
        apply pmv_acc_add; auto. }
      assert (PACC4 : forall y : ProcVar, In y xs -> F1 y = F1' y). {
        subst F1. destruct PMV1 as [(PMV1 & PMV2 & PMV3) | (q'' & PMV1 & PMV2 & PMV3)]; vauto.
        - rewrite pmv_add_iden_l in SAT1.
          red in SAT1. repeat desf.
          intros y PACC4. apply map_eq_In with xs; auto.
        - rewrite PMV1 in SAT1. unfold pmv_add in SAT1. repeat desf.
          red in SAT1. repeat desf.
          intros y PACC4. apply map_eq_In with xs; auto. }

      (* all free variables in the guard and effect of [a] are also in [xs]. *)
      assert (FV1 : forall y : ProcVar, In y (pbexpr_fv (guard a)) -> In y xs). {
        intros y FV1. apply AGR2. unfold act_fv. apply in_or_app. by left. }
      assert (FV2 : forall y : ProcVar, In y (pbexpr_fv (effect a)) -> In y xs). {
        intros y FV2. apply AGR2. unfold act_fv. apply in_or_app. by right. }

      (* fix a process store [ps2] that satisfies the effect of [a] *)
      set (ps2 := expr_denot_map f2 s' : ProcStore).
      generalize SAT4. intro SAT4'. unfold assn_sat in SAT4. subst B2.
      rewrite bexpr_denot_conv with (ps := ps2) in SAT4; auto.

      (* [P'] can perform an [a] action and end up as some process [P''] *)
      assert (PSTEP1 : proc_sos (Pact a) ps1 a Pepsilon ps2). { by apply pstep_act. }
      assert (PSIM1 : proc_bisim P' (Ppar (Palt (Pseq (Pact a) P) Q) R)). {
        destruct PMV1 as [(PMV1 & PMV2 & PMV3) | (q'' & PMV1 & PMV2 & PMV3)]; vauto.
        - rewrite pmv_add_iden_l in SAT1.
          unfold pmv_eq in SAT1. repeat desf.
          rewrite SAT2. by rewrite proc_M1, proc_M4.
        - rewrite PMV1 in SAT1. unfold pmv_add in SAT1. repeat desf.
          unfold pmv_eq in SAT1. repeat desf. }
      assert (PSTEP2 : proc_sos (Ppar (Palt (Pseq (Pact a) P) Q) R) ps1 a (Ppar (Pseq Pepsilon P) R) ps2). {
        by apply pstep_par_l, pstep_alt_l, pstep_seq_l. }
      assert (PSTEP3 : exists P'' : Proc, proc_sos P' ps1 a P'' ps2 /\ proc_bisim P'' (Ppar P R)). {
        inv PSIM1. destruct H as (_ & H & _). apply H in PSTEP2.
        destruct PSTEP2 as (P'' & PSTEP2 & PBISIM2). exists P''. split; vauto.
        rewrite PBISIM2. by rewrite proc_A9. }
      destruct PSTEP3 as (P'' & PSTEP3 & PSIM2).

      (* TODO description *)
      assert (CS1 : forall y : ProcVar, In y ys2 -> phc_concr (ph1b (F1 y)) = phc_snapshot (ph1b' (F1 y))). {
        intros y CS1. subst ph1b'.
        rewrite permheap_conv_proc_mult_apply; auto.
        - apply HV1 in CS1; auto. destruct CS1 as (v & CS1). rewrite CS1. simpls.
        - subst ls2. by apply in_map. }
      assert (CS2 : forall y : ProcVar, In y ys1 -> phc_concr (ph1a (F1 y)) = phc_snapshot (ph1a (F1 y))). {
        intros y CS2. apply HV2 in CS2. destruct CS2 as (? & ? & CS2). rewrite CS2. vauto. }
      assert (CS3 : forall y : ProcVar, In y ys2 -> phc_concr (ph1a (F1 y)) = phc_snapshot (ph1a (F1 y))). {
        intros y CS3. rewrite HV4; vauto. }
      assert (CS4 : forall y : ProcVar, In y ys1 -> phc_concr (ph1b (F1 y)) = phc_snapshot (ph1b' (F1 y))). {
        intros y CS4. subst ph1b'.
        assert (IN1 : ~ In y ys2). { intro IN1. by apply LDISJ3 with y. }
        assert (IN2 : ~ In (expr_denot_map f1 s' y) ls2). {
          intro IN2. apply LDISJ2 with (expr_denot_map f1 s' y); vauto.
          subst ls1. by apply in_map. }
        rewrite <- permheap_conv_proc_mult_pres; vauto.
        apply HV3 in CS4. destruct CS4 as [CS4 | CS4].
        - subst F1. rewrite CS4. vauto.
        - destruct CS4 as (? & ? & ? & CS4). subst F1. rewrite CS4. vauto. }
      assert (CS5 : forall y : ProcVar, In y xs -> phc_concr (ph1b (F1 y)) = phc_snapshot (ph1b' (F1 y))). {
        intros y CS5. apply PERM4 in CS5. destruct CS5 as [CS5 | CS5].
        - by apply CS4.
        - by apply CS1. }
      assert (CS6 : forall y : ProcVar, In y xs -> phc_concr (ph1a (F1 y)) = phc_snapshot (ph1a (F1 y))). {
        intros y CS6. apply PERM4 in CS6. destruct CS6 as [CS6 | CS6].
        - by apply CS2.
        - by apply CS3. }
      assert (CS7 : forall y : ProcVar, In y xs ->
          phc_concr (permheap_add ph1a ph1b (F1 y)) = phc_snapshot (permheap_add ph1a ph1b' (F1 y))). {
        intros y CS7. apply phc_concr_snapshot_compat; auto. }
      assert (CS8 : forall y : ProcVar, In y xs ->
          phc_concr (permheap_add ph1a ph1b (F1 y)) = phc_snapshot (permheap_conv_proc_mult (permheap_add ph1a ph1b) ls2 (F1 y))). {
        intros y CS8. apply CS7 in CS8; auto.
        rewrite permheap_conv_proc_mult_add; auto.
        rewrite permheap_conv_proc_mult_free with (ph := ph1a); auto. }

      (* TODO fix naming *)
      (* the concrete- and snapshot heap contain an element at every location corresponding to variables in [xs] *)
      assert (CSV1 : forall y : ProcVar, In y ys1 -> phc_concr (ph1a (F1 y)) = Some (F2 y)). {
        intros y CSV1. apply HV2 in CSV1. destruct CSV1 as (? & ? & CSV1). rewrite CSV1. vauto. }
      assert (CSV2 : forall y : ProcVar, In y ys1 -> phc_snapshot (ph1a (F1 y)) = Some (F2 y)). {
        intros y CSV2. apply HV2 in CSV2. destruct CSV2 as (? & ? & CSV2). rewrite CSV2. vauto. }
      assert (CSV3 : forall y : ProcVar, In y ys2 -> phc_concr (ph1b (F1 y)) = Some (F2 y)). {
        intros y CSV3. apply HV1 in CSV3. destruct CSV3 as (? & CSV3). rewrite CSV3. vauto. }
      assert (CSV4 : forall y : ProcVar, In y ys2 -> phc_snapshot (ph1b' (F1 y)) = Some (F2 y)). {
        intros y CSV4. subst ph1b'.
        assert (IN1 : In (expr_denot_map f1 s' y) ls2). { subst ls2. by apply in_map. }
        rewrite permheap_conv_proc_mult_apply; auto.
        apply HV1 in CSV4. destruct CSV4 as (? & CSV4). rewrite CSV4. vauto. }
      assert (CSV4' : forall y : ProcVar, In y ys2 -> exists v : Val, phc_snapshot (ph1b (F1 y)) = Some v). {
        intros y CSV4'. apply HV1 in CSV4'. destruct CSV4' as (v & CSV4').
        exists v. rewrite CSV4'. vauto. }
      assert (CSV5 : forall y : ProcVar, In y xs -> phc_concr (permheap_add ph1a ph1b (F1 y)) = Some (F2 y)). {
        intros y CSV5. rewrite PERM4 in CSV5. destruct CSV5 as [CSV5 | CSV5].
        - apply CSV1 in CSV5. by apply phc_concr_add.
        - apply CSV3 in CSV5. rewrite permheap_add_comm.
          apply phc_concr_add; auto. }
      assert (CSV6 : forall y : ProcVar, In y xs -> phc_snapshot (permheap_add ph1a ph1b' (F1 y)) = Some (F2 y)). {
        intros y CSV6. rewrite PERM4 in CSV6. destruct CSV6 as [CSV6 | CSV6].
        - apply CSV2 in CSV6. apply phc_snapshot_add; auto.
        - apply CSV4 in CSV6. rewrite permheap_add_comm.
          apply phc_snapshot_add; auto. }
      assert (CSV6' : forall y : ProcVar, In y xs -> exists v : Val, phc_snapshot (permheap_add ph1a ph1b (F1 y)) = Some v). {
        intros y CSV6'. rewrite PERM4 in CSV6'. destruct CSV6' as [CSV6' | CSV6'].
        - apply CSV2 in CSV6'. exists (F2 y). apply phc_snapshot_add; auto.
        - apply CSV4' in CSV6'. destruct CSV6' as (v & CSV6').
          rewrite permheap_add_comm. exists v. apply phc_snapshot_add; auto. }
      assert (CSV7 : forall y : ProcVar, In y xs -> phc_snapshot (permheap_conv_proc_mult (permheap_add ph1a ph1b) ls2 (F1 y)) = Some (F2 y)). {
        intros y CSV7. apply CSV6 in CSV7; auto.
        rewrite permheap_conv_proc_mult_add; auto.
        rewrite permheap_conv_proc_mult_free with (ph := ph1a); auto. }

      (* TODO description *)
      assert (CSV8 : forall y : ProcVar, In y xs ->
          phc_concr (permheap_add (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) ph3) phJ) phF (F1 y)) =
          phc_concr (permheap_add ph1a ph1b (F1 y))). {
        intros y CSV8. rewrite CSV5; auto.
        apply phc_concr_add, phc_concr_add, phc_concr_add, phc_concr_add; auto. }
      assert (CSV9 : forall y : ProcVar, In y xs ->
          phc_snapshot (permheap_conv_proc_mult (permheap_add (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) ph3) phJ) phF) ls2 (F1 y)) =
          phc_snapshot (permheap_add (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b') ph2) ph3) phJ) phF (F1 y))). {
        intros y CSV9. subst ph1b'.
        repeat rewrite permheap_conv_proc_mult_add; auto.
        rewrite permheap_conv_proc_mult_free with (ph := phF); auto.
        rewrite permheap_conv_proc_mult_free with (ph := phJ); auto.
        rewrite permheap_conv_proc_mult_free with (ph := ph3); auto.
        rewrite permheap_conv_proc_mult_free with (ph := ph2); auto.
        rewrite permheap_conv_proc_mult_free with (ph := ph1a); auto. }
      assert (CSV10 : forall y : ProcVar, In y xs ->
          phc_snapshot (permheap_conv_proc_mult (permheap_add (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) ph3) phJ) phF) ls2 (F1 y)) =
          phc_snapshot (permheap_conv_proc_mult (permheap_add ph1a ph1b) ls2 (F1 y))). {
        intros y CSV10. rewrite CSV9, CSV7; auto.
        apply phc_snapshot_add, phc_snapshot_add, phc_snapshot_add, phc_snapshot_add; auto. }
      assert (CSV11 : forall y : ProcVar, In y xs ->
          phc_snapshot (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) ph3 (F1 y)) =
          phc_snapshot (permheap_add ph1a ph1b (F1 y))). {
        intros y CSV11. apply CSV6' in CSV11; auto.
        destruct CSV11 as (v & CSV11). rewrite CSV11.
        apply phc_snapshot_add, phc_snapshot_add; auto. }
      assert (CSV12 : forall y : ProcVar, In y xs ->
          phc_snapshot (permheap_add (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) ph3) phJ) phF (F1 y)) =
          phc_snapshot (permheap_add ph1a ph1b (F1 y))). {
        intros y CSV12. apply CSV6' in CSV12; auto.
        destruct CSV12 as (v & CSV12). rewrite CSV12.
        apply phc_snapshot_add, phc_snapshot_add, phc_snapshot_add, phc_snapshot_add; auto. }

      (* TODO description *)
      assert (PS1 : forall y : ProcVar, In y xs -> phc_snapshot (permheap_add ph1a ph1b' (F1 y)) = Some (ps2 y)). {
        intros y PS1. rewrite CSV6; auto. }
      assert (PS2 : forall y : ProcVar, In y xs -> phc_snapshot (permheap_conv_proc_mult (permheap_add ph1a ph1b) ls2 (F1 y)) = Some (ps2 y)). {
        intros y PS2. apply PS1 in PS2; auto.
        rewrite permheap_conv_proc_mult_add; auto.
        rewrite permheap_conv_proc_mult_free with (ph := ph1a); auto. }
      assert (PS3 : forall y : ProcVar, In y xs -> phc_concr (permheap_add ph1a ph1b (F1 y)) = Some (ps2 y)). {
        intros y PS3. rewrite CSV5; auto. }

      pose (pmv' := PMelem q' p P'' xs F1').
      pose (pm'' := update pm' (g x) pmv').
      pose (pmv'' := pmv_add (pmv_add (pmv_add (pm (g x)) (pm'' (g x))) (pmJ (g x))) (pmF (g x))).

      (* TODO description *)
      assert (PC1 : exists q' Q',
          pmv_eq (pmv_add (pm (g x)) (pm' (g x))) (PMelem q' p (Ppar P' Q') xs F1') /\
          pmv_eq (pmv_add (pm (g x)) pmv') (PMelem q' p (Ppar P'' Q') xs F1')). {
        subst pmv'. red in D1. specialize D1 with (g x).
        unfold pmv_add. red in D1. clear PMV1. repeat desf.
        - exists (q0 + q'), P0. split; by rewrite proc_M1.
        - exists q', Pepsilon. split; by rewrite proc_M1, proc_M4. }
      destruct PC1 as (q1 & Q1 & PC1 & PC1').
      assert (PC2 : exists q' Q',
          pmv_eq (pmv_add (PMelem q1 p (Ppar P' Q1) xs F1') (pmJ (g x))) (PMelem q' p (Ppar P' Q') xs F1') /\
          pmv_eq (pmv_add (PMelem q1 p (Ppar P'' Q1) xs F1') (pmJ (g x))) (PMelem q' p (Ppar P'' Q') xs F1')). {
        subst pmv'. red in D4. specialize D4 with (g x).
        rewrite PC1 in D4. unfold pmv_add. red in D4. clear PMV1. repeat desf.
        - exists (q1 + q0), (Ppar Q1 P0). split; by rewrite proc_M2.
        - exists q1, Q1. split; vauto. }
      destruct PC2 as (q2 & Q2 & PC2 & PC2').
      rewrite <- PC1 in PC2. rewrite <- PC1' in PC2'.
      assert (PC3 : exists q' Q',
          pmv_eq (pmv_add (PMelem q2 p (Ppar P' Q2) xs F1') (pmF (g x))) (PMelem q' p (Ppar P' Q') xs F1') /\
          pmv_eq (pmv_add (PMelem q2 p (Ppar P'' Q2) xs F1') (pmF (g x))) (PMelem q' p (Ppar P'' Q') xs F1')). {
        subst pmv'. red in D5. specialize D5 with (g x).
        rewrite PC2 in D5. unfold pmv_add. red in D5. clear PMV1. repeat desf.
        - exists (q2 + q0), (Ppar Q2 P0). split; by rewrite proc_M2.
        - exists q2, Q2. split; vauto. }
      destruct PC3 as (q3 & Q3 & PC3 & PC3').
      rewrite <- PC2 in PC3. rewrite <- PC2' in PC3'.
      assert (PC4 : pmv_eq (pmC (g x)) (PMelem q3 p (Ppar P' Q3) xs F1')). {
        red in H1. specialize H1 with (g x). by rewrite H1 in PC3. }
      assert (PC5 : pmv_eq pmv'' (PMelem q3 p (Ppar P'' Q3) xs F1')). {
        subst pmv'' pm''. repeat rewrite update_apply. by rewrite PC3'. }
      clear PC1 PC1' Q1 q1 PC2 PC2' Q2 q2 PC3 PC3'.

      pose (pmC' := update pmC (g x) (PMelem q3 p (Ppar P'' Q3) xs F1')).

      (* TODO descriptions *)
      assert (PAGR1 : procmap_agree pm' pm''). {
        subst pm''. intro pid. clear PMV1. unfold update. desf. rewrite AGR1. vauto. }
      assert (PAGR2 : procmap_agree (procmap_add pm pm') (procmap_add pm pm'')). {
        by apply procmap_agree_add_r. }
      assert (PAGR3 : procmap_agree (procmap_add (procmap_add pm pm') pmJ) (procmap_add (procmap_add pm pm'') pmJ)). {
        by apply procmap_agree_add_l. }
      assert (PAGR4 : procmap_agree pmC pmC'). {
        subst pmC' pmv''. rewrite <- H1. rewrite <- PC5.
        repeat rewrite procmap_add_upd.
        repeat rewrite <- update_idle.
        replace (pm'' (g x)) with pmv'; vauto.
        - replace (update pm' (g x) pmv') with pm''; vauto.
          by apply procmap_agree_add_l.
        - subst pm''. by rewrite update_apply. }

      (* TODO description *)
      assert (PDJ1 : procmap_disj pm pm''). {
        by rewrite <- PAGR1. }
      assert (PDJ2 : procmap_disj (procmap_add (procmap_add (procmap_add pm1a pm1b) pm2) pm3) pm''). {
        rewrite <- PAGR1. by rewrite H8, H6, H4. }
      assert (PDJ3 : procmap_disj (procmap_add (procmap_add pm1a pm1b) pm2) pm''). {
        apply procmap_disj_add_l with pm3; auto.
        - symmetry. by rewrite H8, H6.
        - by rewrite procmap_add_comm. }
      assert (PDJ4 : procmap_disj (procmap_add pm1a pm1b) pm''). {
        apply procmap_disj_add_l with pm2; auto.
        - symmetry. by rewrite H8.
        - by rewrite procmap_add_comm. }

      exists (procmap_add pm pm''), pmJ, pmC'. repeat split; vauto.

      { (* [pm + pm''] is disjoint with [pmJ] *)
      by rewrite <- PAGR2. }
      { (* [pm + pm'' + pmJ] is disjoint with [pmF] *)
      by rewrite <- PAGR3. }
      { (* the composition of [pmC'] is proper *)
      subst pm''.
      rewrite update_idle with pm (g x).
      rewrite update_idle with pmJ (g x).
      rewrite update_idle with pmF (g x).
      repeat rewrite <- procmap_add_upd.
      subst pmC' pmv''.  rewrite <- PC5.
      rewrite <- H1. by rewrite update_apply. }
      { (* [pmC'] is finite *)
      by rewrite <- PAGR4. }
      { (* [pmC'] is well-structured *)
      by rewrite <- PAGR4. }

      { (* [pmC'] is covered by the new snapshot heap *)
      apply procmap_covers_agree with pmC; auto.
      apply procmap_covers_occ with (permheap_snapshot (permheap_add (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) ph3) phJ) phF)); auto.
      unfold permheap_snapshot. intros l IN1. subst ph1b'.
      rewrite <- permheap_conv_proc_mult_free with ls2 ph1a; auto.
      rewrite <- permheap_conv_proc_mult_free with ls2 ph2; auto.
      rewrite <- permheap_conv_proc_mult_free with ls2 ph3; auto.
      rewrite <- permheap_conv_proc_mult_free with ls2 phJ; auto.
      rewrite <- permheap_conv_proc_mult_free with ls2 phF; auto.
      repeat rewrite <- permheap_conv_proc_mult_add; auto.
      assert (IN2 : In l ls2 \/ ~ In l ls2). { by apply classic. }
      intro IN3. apply IN1. destruct IN2 as [IN2 | IN2].
      - subst ls2. apply in_map_iff in IN2.
        destruct IN2 as (y & IN2 & IN2'). clarify.
        assert (IN4 : In y xs). { rewrite PERM4. by right. }
        rewrite CSV10 in IN3; auto. rewrite CSV7 in IN3; vauto.
      - rewrite <- permheap_conv_proc_mult_pres in IN3; auto. }

      { (* [pmC'] is safe with the new snapshot heap *)
      rewrite <- permheap_conv_proc_mult_free with ls2 ph1a; auto.
      rewrite <- permheap_conv_proc_mult_free with ls2 ph2; auto.
      rewrite <- permheap_conv_proc_mult_free with ls2 ph3; auto.
      rewrite <- permheap_conv_proc_mult_free with ls2 phJ; auto.
      rewrite <- permheap_conv_proc_mult_free with ls2 phF; auto.
      subst ph1b'. repeat rewrite <- permheap_conv_proc_mult_add; vauto.
      subst pmC'. intro pid. unfold update.
      destruct (Z.eq_dec (g x) pid); vauto.
      (* [pid] is equal to [g x] *)
      - red. intros ps IN1.
        red in PSAFE1. specialize PSAFE1 with (g x).
        rewrite PC4 in PSAFE1. red in PSAFE1.
        specialize PSAFE1 with ps1.
        (* the process [Ppar P' Q3] is safe with the process store [ps] *)
        assert (PSAFE2 : proc_valid (snd (env p)) (Ppar P' Q3) ps1). {
          apply PSAFE1. intros y PSAFE2.
          rewrite <- AGR4, AGR3; auto. rewrite <- PACC4; auto.
          unfold permheap_snapshot. rewrite CSV11; auto. }
        (* the process stores [ps] and [ps2] agree on all free variables on [a] *)
        assert (IN2 : forall y : ProcVar, In y xs -> ps2 y = ps y). {
          intros y IN2. cut (Some (ps2 y) = Some (ps y)); [intuition vauto|].
          rewrite <- IN1, <- PS2; auto. unfold permheap_snapshot. symmetry.
          rewrite <- PACC4; auto. }
        assert (IN3 : pstore_agree (act_fv a) ps2 ps). {
          intros y IN3. by apply IN2, AGR2. }
        inv PSAFE2. destruct H as (_ & H).
        apply H with a. apply pstep_par_l.
        by apply proc_sos_act_agree with ps2.
      (* [pid] is not equal to [g x] *)
      - red in PSAFE1. specialize PSAFE1 with pid.
        apply pmv_safe_heap_acc with (permheap_snapshot (permheap_add (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) ph3) phJ) phF)); auto.
        intros l ACC1.
        assert (ACC2 : ~ In l (pmv_acc (pmC (g x)))). {
          intro ACC2. red in WS1. apply WS1 with (pid2 := g x) in ACC1; auto. }
        assert (ACC3 : ~ In l ls). { intro ACC3. by apply ACC2, PACC3. }
        unfold permheap_snapshot.
        rewrite <- permheap_conv_proc_mult_pres; auto. }

      exists g, Cskip. repeat split; vauto.

      { (* the ghost semantics can make a step *)
      apply gsos_act_skip with (P := Ppar P' Q3)(ps1 := ps1)(ps2 := ps2); vauto.
      + intros y IN1. rewrite <- PACC4; auto.
      + intros y IN1. rewrite <- PACC4; auto.
        unfold permheap_concr. rewrite CSV8; auto. }

      apply safe_done. rewrite <- H4, <- H6, <- H8.
      rewrite procmap_add_swap_r with (pm3 := pm'').
      exists (permheap_add (permheap_add ph1a ph1b') ph2), ph3.
      repeat split; vauto.
      exists (procmap_add (procmap_add (procmap_add pm1a pm1b) pm2) pm'').
      exists pm3. repeat split; vauto.

      { (* TODO description *)
      apply procmap_disj_swap_r; auto.
      by rewrite H8, H6. }

      rewrite procmap_add_swap_r with (pm3 := pm'').
      exists (permheap_add ph1a ph1b'), ph2. repeat split; vauto.
      exists (procmap_add (procmap_add pm1a pm1b) pm''), pm2. repeat split; vauto.

      { (* TODO description *)
      apply procmap_disj_swap_r; auto.
      by rewrite H8. }

      rewrite <- permheap_add_iden_l with (ph := permheap_add ph1a ph1b').
      exists (permheap_add ph1a ph1b'), permheap_iden. repeat split; auto.
      exists (procmap_add pm1a pm1b), pm''. repeat split; vauto.

      { (* TODO description *)
      apply assn_sat_pointsto_iter_permut with (xs0 := ys1 ++ ys2); auto.
      rewrite <- pointsto_iter_app.
      apply assn_sat_iter_add_l.
      exists ph1a, ph1b'. repeat split; vauto.
      exists pm1a, pm1b. repeat split; vauto.
      subst ph1b'. by apply pointsto_iter_conv_act_proc. }

      { (* TODO description *)
      unfold assn_sat. subst pm''. exists pmv. split; vauto.
      rewrite update_apply. subst pmv'. rewrite PSIM2.
      destruct PMV1 as [(PMV1 & PMV2 & PMV3) | (q'' & PMV1 & PMV2 & PMV3)]; vauto.
      - rewrite pmv_add_iden_l, proc_M1, proc_M4. vauto.
      - rewrite PMV1. unfold pmv_add. desf. }

    (* the program [C] is not empty *)
    + destruct SAFE1 as (_ & _ & _ & _ & SAFE1).

      (* the program transition did not affect the evaluation of [f1] for every process variable in [xs] *)
      assert (PRES1 : forall y : ProcVar, expr_denot (f1 y) s = expr_denot (f1 y) s'). {
        intros y. apply expr_agree. red. intros z IN1.
        apply prog_sos_fv_mod in H3. destruct H3 as (_ & _ & H3).
        apply H3. intro MOD1. unfold disjoint in DISJ1.
        apply DISJ1 with (y := y)(x := z); auto.
        by rewrite cmd_mod_plain. }
      assert (PRES2 : forall y : ProcVar, expr_denot_map f1 s y = expr_denot_map f1 s' y). {
        intros y. unfold expr_denot_map. by apply PRES1. }

      apply SAFE1 with (pmJ := pmJ)(pmF := procmap_add pm' pmF)(pmC := pmC) in H3; vauto; clear SAFE1.
      destruct H3 as (ph' & phJ' & D7 & D8 & H2 & FIN3 & BASIC2 & H3).
      destruct H3 as (pm'' & pmJ' & pmC' & D9 & D10 & H3 & FIN4 & WS2 & BASIC3 & COV2 & PSAFE2 & H4).
      destruct H4 as (g' & C'' & H4 & GSTEP & INV1 & SAFE). clarify.
      intuition desf. generalize GSTEP. intro GSTEP'.
      apply ghost_sos_basic_ghostdata_pres in GSTEP'; auto. desf.

      exists ph', phJ'. repeat split; vauto.
      exists (procmap_add pm'' pm'), pmJ', pmC'. repeat split; vauto.

      { (* the process maps [pm'' + pm'] and [pmJ'] are disjoint *)
      by rewrite <- H5, <- H6. }
      { (* the process maps [pm'' + pm' + pmJ'] and [pmF] are disjoint *)
      by rewrite <- H5, <- H6. }
      { (* the process maps [pm'' + pm' + pmJ' + pmF] and [pmC] are equal *)
      by rewrite <- H5, <- H6. }

      exists g', (Cinact (g' x, a, hs) C''). repeat split; vauto.
      apply IH with (Q := Q)(ys1 := ys1)(ys2 := ys2); vauto.

      { (* the metadata of the active action is still agreed upon *)
      rewrite <- H4. by apply metadata_agree_F with (expr_denot_map f1 s). }

      { (* the free variables of [f1 y] are still disjoint with [cmd_mod C''] for every [y] in [xs] *)
      intros y. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (_ & GSTEP & _).
      red. intros z IN1 IN2. unfold disjoint in DISJ1.
      apply DISJ1 with (y := y)(x := z); auto. }

      { (* the program variable [x] is not modified by [C''] *)
      intros IN1. apply DISJ2. apply ghost_sos_fv_mod in GSTEP.
      destruct GSTEP as (_ & GSTEP & _). by apply GSTEP. }

      { (* the program [C''] is still basic *)
      apply ghost_sos_basic_pres in GSTEP; vauto. }

      { (* the process maps [pm''] and [pm'] are disjoint *)
      by rewrite <- H5. }

      { (* the process map [pm'] still satisfies the process ownership assertion *)
      apply assn_sat_agree with (s1 := s); auto.
      intros y IN1. simpl in IN1. destruct IN1 as [IN1 | IN1]; vauto.
      - apply ghost_sos_fv_mod in GSTEP.
        destruct GSTEP as (_ & _ & GSTEP & _). by apply GSTEP.
      - unfold expr_map_fv in IN1. destruct IN1 as (z & IN1).
        apply ghost_sos_fv_mod in GSTEP.
        destruct GSTEP as (_ & _ & GSTEP & _).
        apply GSTEP; vauto. intro H2. unfold disjoint in DISJ1.
        apply DISJ1 with (y := z)(x := y); vauto. }

      { (* the process maps [pm] and [pmJ] are disjoint *)
      apply procmap_disj_add_l with pm'; auto.
      by rewrite procmap_add_comm. }

      { (* the process maps [pm + pmJ] and [pm' + pmF] are disjoint *)
      assert (K1 : procmap_disj pmJ pmF). {
        apply procmap_disj_add_l with (procmap_add pm pm'); auto. }
      apply procmap_disj_compat; auto.
      apply procmap_disj_assoc_l; auto. }

      { (* the process maps [pm + pmJ + pm' + pmF] equals [pmC] up to bisimulation *)
      rewrite <- procmap_add_assoc.
      by rewrite procmap_add_swap_r with (pm3 := pm'). }
Qed.


Theorem rule_act (env : ProcEnv) :
  forall x a C xs J q p P Q (f1 f2 f2' : ProcVar -> Expr)(fq : ProcVar -> Qc) A1 A2,
  let B1 := pbexpr_convert (guard a) f2 in
  let B2 := pbexpr_convert (effect a) f2' in
    (forall y, In y (act_fv a) -> In y xs) ->
    (forall y : ProcVar, In y xs -> perm_valid (fq y)) ->
    (forall y : ProcVar, disjoint (expr_fv (f1 y)) (cmd_mod C)) ->
  ~ cmd_mod C x ->
  csl env True J (Astar (Astar (Aiter (pointsto_iter_procact xs fq f1 f2)) (Aplain B1)) A1) C (Astar (Astar (Aiter (pointsto_iter_procact xs fq f1 f2')) (Aplain B2)) A2) ->
  csl env False J
    (Astar (Astar (Astar (Aiter (pointsto_iter xs fq f1 f2 PTTproc)) (Aproc x q p (Palt (Pseq (Pact a) P) Q) xs f1)) (Aplain B1)) A1)
    (Cact x a C)
    (Astar (Astar (Astar (Aiter (pointsto_iter xs fq f1 f2' PTTproc)) (Aproc x q p P xs f1)) (Aplain B2)) A2).
Proof.
  intros x a C xs J q p P Q f1 f2 f2' fq A1 A2 B1 B2 FV1 VF1 VF2 VF3 CSL.
  red. split; vauto.

  { (* [Cact x a C] is a user program *)
  simpl. by destruct CSL as (? & _). }

  intros ENV [|n] ph pm s g V1 V2 WF1 SAT1. vauto.
  set (F1 := expr_denot_map f1 s : ProcVar -> Val).
  set (F2 := expr_denot_map f2 s : ProcVar -> Val).
  repeat split; vauto.

  (* (2) absence of faults *)
  - red. intros phF pmF D1 D2 FIN1 FIN2 ABORT1. inv ABORT1.

  (* (5) program step *)
  - simpl. intros phJ phF pmJ pmF pmC h' s' C' D1 D2 D3 D4 H1 FIN1 WS1 INV FIN2 COV1 PSAFE1 STEP.
    inv STEP. apply assn_star_assoc_r, assn_star_assoc_r in SAT1; vauto.
    destruct SAT1 as (ph1 & ph2 & D5 & H2 & pm1 & pm2 & D6 & H3 & SAT1 & SAT2). clarify.

    (* [xs] can be split into two lists, one with read-only permissions and the other with write permissions *)
    assert (K1 : exists ys1 ys2 : list ProcVar,
        Permutation xs (ys1 ++ ys2) /\
        (forall x : ProcVar, In x ys1 -> fq x <> perm_full) /\
        (forall x : ProcVar, In x ys2 -> fq x = perm_full)). {
      pose (f := fun x : ProcVar => if Qc_eq_dec (fq x) perm_full then false else true).
      pose (ys := partition f xs).
      exists (fst ys), (snd ys). repeat split.
      - apply partition_permut with f. by apply partition_res.
      - intros y H2. apply partition_f_left with (xs0 := xs)(ys2 := snd ys)(f0 := f) in H2; auto.
        + subst f. simpls. desf.
        + by apply partition_res.
      - intros y H2. apply partition_f_right with (xs0 := xs)(ys1 := fst ys)(f0 := f) in H2; auto.
        + subst f. simpls. desf.
        + by apply partition_res. }
    destruct K1 as (ys1 & ys2 & H2 & H4 & H5).

    (* any variable [y] is in [xs] iff [y] is in [ys1] or [ys2] *)
    assert (LDISJ1 : forall y : ProcVar, In y xs <-> In y ys1 \/ In y ys2). {
      intro y. split; intro H8.
      - apply Permutation_in with (x := y) in H2; auto.
        apply in_app_or in H2. destruct H2 as [H2 | H2]; vauto.
      - symmetry in H2. apply Permutation_in with (x := y) in H2; auto.
        by apply in_or_app. }

    (* [ph1] and [pm1] are both valid *)
    assert (V3 : permheap_valid ph1). { by apply permheap_disj_valid_l in D5. }
    assert (V4 : procmap_valid pm1). { by apply procmap_disj_valid_l in D6. }

    (* split the iterated separating conjunction in SAT1 into a process- and an action part *)
    generalize SAT1. intro SAT1'.
    apply assn_sat_pointsto_iter_permut with (ys := ys1 ++ ys2) in SAT1; auto.
    rewrite <- pointsto_iter_app in SAT1. apply assn_iter_add_r in SAT1; auto.
    destruct SAT1 as (ph1a & ph1b & D7 & H6 & pm1a & pm1b & D8 & H7 & SAT1a & SAT1b). clarify.
    generalize SAT1b. intro SAT1b'. apply pointsto_iter_conv_proc_act in SAT1b.
    set (ls := map F1 xs : list Loc).
    set (ls1 := map F1 ys1 : list Loc).
    set (ls2 := map F1 ys2 : list Loc).
    set (ph1b' := permheap_conv_act_mult ph1b ls2).
    replace (map (expr_denot_map f1 s') ys2) with (ls2) in SAT1b; auto.
    replace (permheap_conv_act_mult ph1b ls2) with ph1b' in SAT1b; auto.

    (* location [l] is in [ls] iff [l] is in [ls1] or [ls2] *)
    assert (LDISJ2 : forall l : Loc, In l ls <-> In l ls1 \/ In l ls2). {
      intro l. split; intro H8.
      - subst ls. apply in_map_iff in H8.
        destruct H8 as (y & H8 & H9). clarify.
        apply LDISJ1 in H9. destruct H9 as [H9 | H9].
        + left. subst ls1. by apply in_map.
        + right. subst ls2. by apply in_map.
      - destruct H8 as [H8 | H8].
        + subst ls1. apply in_map_iff in H8.
          destruct H8 as (y & H8 & H9). clarify.
          subst ls. apply in_map, LDISJ1. by left.
        + subst ls2. apply in_map_iff in H8.
          destruct H8 as (y & H8 & H9). clarify.
          subst ls. apply in_map, LDISJ1. by right. }

    (* the concrete- and snapshot heap contain an element at every location corresponding to variables in [xs] *)
    assert (HC1 : forall y : ProcVar, In y xs ->
        exists q : Qc, perm_valid q /\ permheap_add ph1a ph1b (F1 y) = PHCproc q (F2 y)). {
      intros y HC1. apply pointsto_iter_sat_single_proc with (x0 := y) in SAT1'; auto.
      apply phc_le_diff in SAT1'; vauto.
      - destruct SAT1' as (phc & D11 & SAT1').
        unfold phc_disj in D11. repeat desf; vauto.
        unfold phc_add in SAT1'. desf. exists (fq y + q0).
        intuition vauto. by apply perm_add_valid.
      - simpl. by apply VF1. }
    assert (HCL1 : forall l : Loc, In l ls -> exists q v, perm_valid q /\ permheap_add ph1a ph1b l = PHCproc q v). {
      intros l HCL1. subst ls. apply in_map_iff in HCL1.
      destruct HCL1 as (y & ? & HCL1). desf.
      apply HC1 in HCL1. destruct HCL1 as (q' & ? & ?).
      exists q'. intuition vauto. }
    assert (HC2 : forall y : ProcVar, In y ys2 -> ph1b (F1 y) = PHCproc perm_full (F2 y)). {
      intros y HC2. subst ph1b'.
      apply pointsto_iter_sat_single_proc with (x0 := y) in SAT1b'; auto.
      rewrite H5 in SAT1b'; auto.
      apply phc_le_full_eq in SAT1b'; vauto.
      by apply permheap_disj_valid_r in D7. }
    assert (HCL2 : forall l : Loc, In l ls2 -> exists v : Val, ph1b l = PHCproc perm_full v). {
      intros l HCL2. subst ls2. apply in_map_iff in HCL2.
      destruct HCL2 as (y & ? & HCL2). desf.
      apply HC2 in HCL2. rewrite HCL2. by exists (F2 y). }
    assert (HC3 : forall y : ProcVar, In y ys1 -> exists q : Qc, perm_valid q /\ ph1a (F1 y) = PHCproc q (F2 y)). {
      intros y HC3. apply pointsto_iter_sat_single_proc with (x0 := y) in SAT1a; auto.
      apply phc_le_diff in SAT1a; vauto.
      - destruct SAT1a as (phc & D11 & SAT1a).
        subst F1. unfold expr_denot_map. rewrite <- SAT1a.
        unfold phc_disj in D11. destruct phc as [|q'|q'|q'|]; vauto.
        unfold phc_add. desf. exists (fq y + q'); split; vauto.
        by apply perm_add_valid.
      - simpl. apply VF1. rewrite LDISJ1. by left.
      - by apply permheap_disj_valid_l in D7. }
    assert (HCL3 : forall l : Loc, In l ls1 -> exists q v, perm_valid q /\ ph1a l = PHCproc q v). {
      intros l HCL3. subst ls1. apply in_map_iff in HCL3.
      destruct HCL3 as (y & ? & HCL3). desf. apply HC3 in HCL3. unfold expr_denot_map.
      destruct HCL3 as (q' & HCL3). by exists q', (expr_denot (f2 y) s'). }
    assert (HC4 : forall y : ProcVar, In y ys1 -> ph1b (F1 y) = PHCfree \/ exists q, perm_valid q /\ ph1b (F1 y) = PHCproc q (F2 y)). {
      intros y HC4. assert (IN1 : In y xs). { apply LDISJ1. by left. }
      apply HC3 in HC4. destruct HC4 as (q' & ? & HC4).
      apply HC1 in IN1. destruct IN1 as (q'' & ? & IN1).
      red in D7. specialize D7 with (F1 y). rewrite HC4 in D7.
      red in D7. unfold permheap_add in IN1. repeat desf; vauto.
      right. exists q0. intuition vauto. by apply perm_disj_valid_r in D7. }
    assert (HCL4 : forall l : Loc, In l ls1 -> ph1b l = PHCfree \/ exists q v, perm_valid q /\ ph1b l = PHCproc q v). {
      intros l HCL4. subst ls1. apply in_map_iff in HCL4.
      destruct HCL4 as (y & ? & HCL4). clarify.
      apply HC4 in HCL4. destruct HCL4 as [HCL4 | (q' & ? & HCL4)]; vauto.
      right. exists q', (F2 y). vauto. }
    assert (HC5 : forall y : ProcVar, In y ys2 -> ph1a (F1 y) = PHCfree). {
      intros y HC5. apply HC2 in HC5.
      red in D7. specialize D7 with (F1 y). rewrite HC5 in D7.
      symmetry in D7. apply phc_disj_full_free in D7; vauto. }
    assert (HCL5 : forall l : Loc, In l ls2 -> ph1a l = PHCfree). {
      intros l HCL5. subst ls2. apply in_map_iff in HCL5.
      destruct HCL5 as (y & ? & HCL5). clarify. by apply HC5 in HCL5. }
    assert (HC6 : forall y : ProcVar, In y xs -> ph2 (F1 y) = PHCfree \/ exists q, perm_valid q /\ ph2 (F1 y) = PHCproc q (F2 y)). {
      intros y HC6. apply HC1 in HC6. destruct HC6 as (q' & ? & HC6).
      red in D5. specialize D5 with (F1 y). rewrite HC6 in D5.
      red in D5. repeat desf; vauto. right. exists q0. intuition vauto.
      by apply perm_disj_valid_r in D5. }
    assert (HCL6 : forall l : Loc, In l ls -> ph2 l = PHCfree \/ exists q v, perm_valid q /\ ph2 l = PHCproc q v). {
      intros l HCL6. subst ls. apply in_map_iff in HCL6.
      destruct HCL6 as (y & ? & HCL6). clarify.
      apply HC6 in HCL6. destruct HCL6 as [HCL6 | (q' & ? & HCL6)]; vauto.
      right. exists q', (F2 y). split; vauto. }

    (* the sequences [ls1] and [ls2] are disjoint *)
    assert (LDISJ3 : forall l : Loc, In l ls1 -> In l ls2 -> False). {
      intros l H8 H9. apply HCL2 in H9.
      destruct H9 as (v' & H9). apply HCL3 in H8.
      destruct H8 as (q' & v'' & H8 & H10).
      unfold permheap_disj in D7. specialize D7 with l.
      rewrite H9, H10 in D7. unfold phc_disj in D7. desf.
      by apply perm_disj_full_neg_l with q'. }

    (* [ph1b l] is full for every [l] in [ls2]; and [ph1a l], [ph2 l], [phJ l] and [phF l] are all free *)
    assert (HV1 : forall y : ProcVar, In y ys2 -> phc_full (ph1b (F1 y))). {
      intros y HV1. apply HC2 in HV1. by rewrite HV1. }
    assert (HVL1 : forall l : Loc, In l ls2 -> phc_full (ph1b l)). {
      intros y HVL1. apply HCL2 in HVL1. destruct HVL1 as (?&HVL1). by rewrite HVL1. }
    assert (HV2 : forall y : ProcVar, In y ys2 -> ph1a (F1 y) = PHCfree). {
      intros y HV2. apply HC5 in HV2. by rewrite HV2. }
    assert (HVL2 : forall l : Loc, In l ls2 -> ph1a l = PHCfree). {
      intros l HVL2. by apply HCL5. }
    assert (HV3 : forall y : ProcVar, In y ys2 -> ph2 (F1 y) = PHCfree). {
      intros y HV3. red in D5. specialize D5 with (F1 y).
      apply phc_disj_full_free in D5; auto.
      rewrite <- permheap_add_cell. rewrite HV2; auto.
      rewrite phc_add_iden_r. by apply HV1. }
    assert (HVL3 : forall l : Loc, In l ls2 -> ph2 l = PHCfree). {
      intros l HVL3. subst ls2. apply in_map_iff in HVL3.
      destruct HVL3 as (y & ? & HVL3). clarify. by apply HV3. }
    assert (HV4 : forall y : ProcVar, In y ys2 -> phJ (F1 y) = PHCfree). {
      intros y HV4. red in D1. specialize D1 with (F1 y).
      apply phc_disj_full_free in D1; auto.
      repeat rewrite <- permheap_add_cell. rewrite HV2, HV3; auto.
      rewrite phc_add_iden_l, phc_add_iden_r. by apply HV1. }
    assert (HVL4 : forall l : Loc, In l ls2 -> phJ l = PHCfree). {
      intros l HVL4. subst ls2. apply in_map_iff in HVL4.
      destruct HVL4 as (y & ? & HVL4). clarify. by apply HV4. }
    assert (HV5 : forall y : ProcVar, In y ys2 -> phF (F1 y) = PHCfree). {
      intros y HV5. red in D2. specialize D2 with (F1 y).
      apply phc_disj_full_free in D2; auto.
      repeat rewrite <- permheap_add_cell. rewrite HV2, HV3, HV4; auto.
      rewrite phc_add_iden_l, phc_add_iden_r, phc_add_iden_l. by apply HV1. }
    assert (HVL5 : forall l : Loc, In l ls2 -> phF l = PHCfree). {
      intros l HVL5. subst ls2. apply in_map_iff in HVL5.
      destruct HVL5 as (y & ? & HVL5). clarify. by apply HV5. }

    (* the heap [ph1b'] remains disjoint in all compositions in which [ph1b] is disjoint *)
    assert (DISJ1 : permheap_disj ph1a ph1b'). {
      rewrite <- permheap_conv_act_mult_free with ls2 ph1a; auto.
      by apply permheap_conv_act_mult_disj. }
    assert (DISJ2 : permheap_disj (permheap_add ph1a ph1b') ph2). {
      rewrite <- permheap_conv_act_mult_free with ls2 ph1a; auto.
      rewrite <- permheap_conv_act_mult_free with ls2 ph2; auto.
      subst ph1b' F1. rewrite <- permheap_conv_act_mult_add; vauto.
      by apply permheap_conv_act_mult_disj. }
    assert (DISJ3 : permheap_disj (permheap_add (permheap_add ph1a ph1b') ph2) phJ). {
      rewrite <- permheap_conv_act_mult_free with ls2 ph1a; auto.
      rewrite <- permheap_conv_act_mult_free with ls2 ph2; auto.
      rewrite <- permheap_conv_act_mult_free with ls2 phJ; auto.
      subst ph1b' F1. repeat rewrite <- permheap_conv_act_mult_add; vauto.
      by apply permheap_conv_act_mult_disj. }
    assert (DISJ4 : permheap_disj (permheap_add (permheap_add (permheap_add ph1a ph1b') ph2) phJ) phF). {
      rewrite <- permheap_conv_act_mult_free with ls2 ph1a; auto.
      rewrite <- permheap_conv_act_mult_free with ls2 ph2; auto.
      rewrite <- permheap_conv_act_mult_free with ls2 phJ; auto.
      rewrite <- permheap_conv_act_mult_free with ls2 phF; auto.
      subst ph1b' F1. repeat rewrite <- permheap_conv_act_mult_add; vauto.
      by apply permheap_conv_act_mult_disj. }

    (* the permission heaps [ph2] and [pm2] are valid *)
    assert (V5 : permheap_valid (permheap_add ph1a ph1b')). { by apply permheap_add_valid. }
    assert (V6 : permheap_valid ph2). { by apply permheap_disj_valid_r in D5. }
    assert (V7 : procmap_valid pm2). { by apply procmap_disj_valid_r in D6. }

    (* TODO description *)
    assert (CSV1 : forall y : ProcVar, In y ys1 -> phc_concr (ph1a (F1 y)) = Some (F2 y)). {
      intros y CSV1. apply HC3 in CSV1. destruct CSV1 as (q' & ? & CSV1). by rewrite CSV1. }
    assert (CSVL1 : forall l : Loc, In l ls1 -> exists v : Val, phc_concr (ph1a l) = Some v). {
      intros l CSVL1. apply HCL3 in CSVL1. destruct CSVL1 as (? & v' & ? & CSVL1).
      rewrite CSVL1. by exists v'. }
    assert (CSV2 : forall y : ProcVar, In y ys2 -> phc_concr (ph1a (F1 y)) = None). { ins. by rewrite HC5. }
    assert (CSVL2 : forall l : Loc, In l ls2 -> phc_concr (ph1a l) = None). { ins. by rewrite HCL5. }
    assert (CSV3 : forall y : ProcVar, In y ys2 -> phc_concr (ph1b (F1 y)) = Some (F2 y)). {
      intros y CSV3. apply HC2 in CSV3. rewrite CSV3. vauto. }
    assert (CSVL3 : forall l : Loc, In l ls2 -> exists v : Val, phc_concr (ph1b l) = Some v). {
      intros l CSVL3. apply HCL2 in CSVL3. destruct CSVL3 as (v' & CSVL3). rewrite CSVL3. by exists v'. }
    assert (CSV4 : forall y : ProcVar, In y xs -> phc_concr (permheap_add ph1a ph1b (F1 y)) = Some (F2 y)). {
      intros y CSV4. apply LDISJ1 in CSV4. destruct CSV4 as [CSV4 | CSV4].
      - apply CSV1 in CSV4. apply phc_concr_add; auto.
      - apply CSV3 in CSV4. rewrite permheap_add_comm.
        apply phc_concr_add; auto. }
    assert (CSVL4 : forall l : Loc, In l ls -> exists v : Val, phc_concr (permheap_add ph1a ph1b l) = Some v). {
      intros l CSVL4. subst ls. apply in_map_iff in CSVL4.
      destruct CSVL4 as (y & ? & CSVL4). clarify.
      apply CSV4 in CSVL4. by exists (F2 y). }
    assert (CSV5 : forall y : ProcVar, In y xs -> phc_concr (permheap_add (permheap_add ph1a ph1b) ph2 (F1 y)) = Some (F2 y)). {
      intros y CSV5. rewrite <- permheap_add_cell. apply phc_concr_add; auto. }
    assert (CSVL5 : forall l : Loc, In l ls -> exists v, phc_concr (permheap_add (permheap_add ph1a ph1b) ph2 l) = Some v). {
      intros l CSVL5. apply CSVL4 in CSVL5. destruct CSVL5 as (v & CSVL5).
      exists v. rewrite <- permheap_add_cell. apply phc_concr_add; auto. }

    (* relations between the concrete- and snapshot values of [ph1a], [ph1b] and [ph1b'] with respect to [xs] *)
    assert (CS1 : forall y : ProcVar, In y xs -> phc_concr (ph2 (F1 y)) = phc_snapshot (ph2 (F1 y))). {
      intros y CS1. apply HC6 in CS1. destruct CS1 as [CS1 | (q' & ? & CS1)]; by rewrite CS1. }
    assert (CSL1 : forall l : Loc, In l ls -> phc_concr (ph2 l) = phc_snapshot (ph2 l)). {
      intros l CSL1. apply HCL6 in CSL1. destruct CSL1 as [CSL1 | (? & ? & ? & CSL1)]; by rewrite CSL1. }
    assert (CS2 : forall y : ProcVar, In y ys1 -> phc_concr (ph1a (F1 y)) = phc_snapshot (ph1a (F1 y))). {
      intros y CS2. apply HC3 in CS2. destruct CS2 as (? & ? & CS2). by rewrite CS2. }
    assert (CSL2 : forall l : Loc, In l ls1 -> phc_concr (ph1a l) = phc_snapshot (ph1a l)). {
      intros l CSL2. apply HCL3 in CSL2. destruct CSL2 as (?&?&? & CSL2). by rewrite CSL2. }
    assert (CS3 : forall y : ProcVar, In y ys2 -> phc_concr (ph1a (F1 y)) = phc_snapshot (ph1a (F1 y))). {
      intros y CS3. by rewrite HV2. }
    assert (CSL3 : forall l : Loc, In l ls2 -> phc_concr (ph1a l) = phc_snapshot (ph1a l)). {
      intros l CSL3. by rewrite HVL2. }
    assert (CS4 : forall y : ProcVar, In y xs -> phc_concr (ph1a (F1 y)) = phc_snapshot (ph1a (F1 y))). {
      intros y CS4. apply LDISJ1 in CS4. destruct CS4 as [CS4 | CS4]; auto. }
    assert (CSL4 : forall l : Loc, In l ls -> phc_concr (ph1a l) = phc_snapshot (ph1a l)). {
      intros l CSL4. apply LDISJ2 in CSL4. destruct CSL4 as [CSL4 | CSL4]; auto. }
    assert (CS5 : forall y : ProcVar, In y ys2 -> phc_concr (ph1b (F1 y)) = phc_snapshot (ph1b (F1 y))). {
      intros y CS5. apply HC2 in CS5. by rewrite CS5. }
    assert (CSL5 : forall l : Loc, In l ls2 -> phc_concr (ph1b l) = phc_snapshot (ph1b l)). {
      intros l CSL5. apply HCL2 in CSL5. destruct CSL5 as (?&CSL5). by rewrite CSL5. }
    assert (CS6 : forall y : ProcVar, In y ys1 -> phc_concr (ph1b (F1 y)) = phc_snapshot (ph1b (F1 y))). {
      intros y CS6. apply HC4 in CS6. destruct CS6 as [CS6 | (? & ? & CS6)]; by rewrite CS6. }
    assert (CSL6 : forall l : Loc, In l ls1 -> phc_concr (ph1b l) = phc_snapshot (ph1b l)). {
      intros l CSL6. apply HCL4 in CSL6. destruct CSL6 as [CSL6 | (? & ? & ? & CSL6)]; by rewrite CSL6. }
    assert (CS7 : forall y : ProcVar, In y xs -> phc_concr (ph1b (F1 y)) = phc_snapshot (ph1b (F1 y))). {
      intros y CS7. apply LDISJ1 in CS7. destruct CS7 as [CS7 | CS7]; auto. }
    assert (CSL7 : forall l : Loc, In l ls -> phc_concr (ph1b l) = phc_snapshot (ph1b l)). {
      intros l CSL7. apply LDISJ2 in CSL7. destruct CSL7 as [CSL7 | CSL7]; auto. }
    assert (CS8 : forall y : Loc, In y xs ->
        permheap_concr (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) phJ) phF) (F1 y) =
        permheap_concr (permheap_add (permheap_add ph1a ph1b) ph2) (F1 y)). {
      intros y CS8. unfold permheap_concr. rewrite CSV5; auto.
      rewrite <- permheap_add_cell. apply phc_concr_add; auto.
      rewrite <- permheap_add_cell. apply phc_concr_add; auto. }
    assert (CSL8 : forall l : Loc, In l ls ->
        permheap_concr (permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) phJ) phF) l =
        permheap_concr (permheap_add (permheap_add ph1a ph1b) ph2) l). {
      intros l CSL8. subst ls. apply in_map_iff in CSL8.
      destruct CSL8 as (y & ? & CSL8). clarify. auto. }

    (* TODO description *)
    assert (CSR1 : permheap_concr ph1b = permheap_concr ph1b'). {
      subst ph1b'. by rewrite permheap_conv_act_mult_concr. }
    assert (CSRL1 : forall l : Loc, phc_concr (ph1b l) = phc_concr (ph1b' l)). {
      intro l. by apply equal_f with l in CSR1. }
    assert (CSR2 : permheap_snapshot ph1b = permheap_snapshot ph1b'). {
      extensionality l. subst ph1b'. unfold permheap_snapshot.
      assert (IN : In l ls2 \/ ~ In l ls2). { by apply classic. }
      destruct IN as [IN | IN].
      - rewrite permheap_conv_act_mult_apply; auto.
        apply HCL2 in IN. destruct IN as (? & IN). by rewrite IN.
      - by rewrite <- permheap_conv_act_mult_pres. }
    assert (CSRL2 : forall l : Loc, phc_snapshot (ph1b l) = phc_snapshot (ph1b' l)). {
      intro l. by apply equal_f with l in CSR2. }
    assert (CSR3 : forall y : ProcVar, In y xs -> phc_concr (permheap_add ph1a ph1b (F1 y)) = phc_snapshot (permheap_add ph1a ph1b' (F1 y))). {
      intros y CSR3. rewrite <- permheap_add_cell.
      apply phc_concr_snapshot_compat; auto. rewrite CS7, <- CSRL2; auto. }
    assert (CSRL3 : forall l : Loc, In l ls -> phc_concr (permheap_add ph1a ph1b l) = phc_snapshot (permheap_add ph1a ph1b' l)). {
      intros l CSRL3. rewrite <- permheap_add_cell.
      apply phc_concr_snapshot_compat; auto. rewrite CSL7, <- CSRL2; auto. }

    exists (permheap_add (permheap_add ph1a ph1b') ph2), phJ.
    repeat split; vauto.

    { (* the heap concretisation is proper *)
    rewrite <- permheap_conv_act_mult_free with (xs := ls2)(ph := ph1a) at 1; auto.
    rewrite <- permheap_conv_act_mult_free with (xs := ls2)(ph := ph2) at 1; auto.
    rewrite <- permheap_conv_act_mult_free with (xs := ls2)(ph := phJ) at 1; auto.
    rewrite <- permheap_conv_act_mult_free with (xs := ls2)(ph := phF) at 1; auto.
    subst ph1b'. repeat rewrite <- permheap_conv_act_mult_add; vauto.
    by rewrite permheap_conv_act_mult_concr. }

    pose (phC := permheap_add (permheap_add (permheap_add (permheap_add ph1a ph1b) ph2) phJ) phF).
    pose (h := permheap_concr phC).
    pose (hs := permheap_snapshot phC).

    exists pm, pmJ, pmC. repeat split; vauto.

    { (* [pmC] covers the updated snapshot heap *)
    intros l H6. apply procmap_covers_occ with hs; auto.
    rewrite <- permheap_conv_act_mult_free with ls2 ph1a; auto.
    rewrite <- permheap_conv_act_mult_free with ls2 ph2; auto.
    rewrite <- permheap_conv_act_mult_free with ls2 phJ; auto.
    rewrite <- permheap_conv_act_mult_free with ls2 phF; auto.
    subst ph1b'. repeat rewrite <- permheap_conv_act_mult_add; vauto.
    by apply permheap_snapshot_conv_act_mult_occ. }

    { (* [pmC] is safe with the updated snapshot heap *)
    apply procmap_safe_subheap with hs; auto.
    intros l v H6. subst hs phC. rewrite <- H6. unfold permheap_snapshot.
    repeat apply phc_snapshot_disj_add_l; auto.
    apply phc_snapshot_disj_add_r; auto. }

    exists g, (Cinact (g x, a, h) C). repeat split; vauto.

    { (* the resource invariant is still maintained *)
    unfold invariant_sat in INV. simpl in INV.
    intuition vauto. }

    (* take the process ownership predicate in SAT2 apart *)
    destruct SAT2 as (ph3 & ph4 & D9 & EQ1 & pm3 & pm4 & D10 & EQ2 & SAT2a & SAT2b). clarify.
    set (pm' := procmap_add (procmap_add (procmap_add pm1a pm1b) pm4) pm3).
    assert (EQ1 : procmap_eq pm pm'). {
      rewrite <- H3, <- H7, <- EQ2.
      rewrite <- procmap_add_assoc.
      rewrite procmap_add_swap_r with (pm3 := pm4); auto. }

    (* most of the remainder of the proof follows from [safe_action] *)
    rewrite EQ1. subst pm'.
    apply safe_action with Q ys1 ys2; vauto.

    { (* the metadata of the activated action is agreed upon *)
    unfold metadata_agree.
    assert (PS1 : exists q P, pmv_eq (pm3 (g x)) (PMelem q p P xs F1)). {
      unfold assn_sat in SAT2a. destruct SAT2a as (pmv & D11 & SAT2a).
      unfold pmv_disj in D11. repeat desf; vauto.
      - unfold pmv_add in SAT2a. desf.
        exists (q + q0), (Ppar (Palt (Pseq (Pact a) P) Q) P0). vauto. }
    destruct PS1 as (q' & P' & PS1).
    exists q', P'. repeat split; vauto.
    - intros y IN1. subst h phC.
      assert (IN2 : In (expr_denot_map f1 s' y) ls). { subst ls. by apply in_map. }
      rewrite CSL8; auto.
      unfold permheap_concr, permheap_snapshot.
      apply phc_concr_snapshot_compat; auto.
    - exists F2. split; vauto.
      + intros y H8. unfold expr_denot_map.
        subst h phC. unfold permheap_concr.
        rewrite <- permheap_add_cell. apply phc_concr_add; auto.
        rewrite <- permheap_add_cell. apply phc_concr_add; auto.
        rewrite <- permheap_add_cell. apply phc_concr_add; auto.
        apply HC1 in H8. destruct H8 as (q'' & H8 & H9).
        subst F1. unfold expr_denot_map in H9. rewrite H9. simpls.
      + rewrite <- bexpr_denot_conv with (s := s')(f := f2); vauto.
        apply assn_weaken_l in SAT2b; auto.
        * by apply permheap_disj_valid_r in D9.
        * by apply procmap_disj_valid_r in D10. }

    { (* [pm1a + pm1b + pm4] and [pm3] are disjoint *)
    rewrite H7. apply procmap_disj_assoc_r; auto.
    rewrite procmap_add_comm. by rewrite EQ2. }

    (* TODO description *)
    assert (HVL6 : forall l : Loc, In l ls2 -> ph3 l = PHCfree). {
      intros l HVL6. apply HVL3 in HVL6. apply phc_iden_split in HVL6. desf. }
    assert (HVL7 : forall l : Loc, In l ls2 -> ph4 l = PHCfree). {
      intros l HVL7. apply HVL3 in HVL7. apply phc_iden_split in HVL7. desf. }

    apply CSL; vauto.

    { (* the heap [ph1a + ph1b' + ph3 + ph4] is valid *)
    rewrite <- permheap_conv_act_mult_free with (ph := ph1a)(xs := ls2); auto.
    rewrite <- permheap_conv_act_mult_free with (ph := ph3)(xs := ls2); auto.
    rewrite <- permheap_conv_act_mult_free with (ph := ph4)(xs := ls2); auto.
    subst ph1b'. repeat rewrite <- permheap_conv_act_mult_add; vauto.
    by apply permheap_conv_act_mult_valid. }

    { (* the maps [pm1a + pm1b + pm4] is valid *)
    rewrite H7. apply procmap_add_valid.
    apply procmap_disj_add_r with pm3; auto.
    rewrite procmap_add_comm. by rewrite EQ2. }

    { (* the program [C] is well-formed *)
    simpl in WF1. by apply cmd_basic_wf. }

    (* the precondition of the Hoare-triple for [C] is satisfied *)
    apply assn_sat_star_assoc_l.
    exists (permheap_add (permheap_add ph1a ph1b') ph3), ph4.
    repeat split; vauto.
    { (* [ph1a + ph1b' + ph3] and [ph4] are disjoint *)
    apply permheap_disj_assoc_r; auto. }
    exists (procmap_add pm1a pm1b), pm4.
    repeat split; vauto.
    { (* [pm1a + pm1b] and [pm4] are disjoint *)
    rewrite H7. apply procmap_disj_add_r with pm3; auto.
    rewrite procmap_add_comm. by rewrite EQ2. }
    rewrite <- procmap_add_iden_l with (procmap_add pm1a pm1b).
    apply assn_sat_weaken; auto.
    { (* [ph1a + ph1b] and [ph3] are disjoint *)
    apply permheap_disj_add_r with ph4; auto. }
    apply assn_sat_procact_iter_permut with (xs0 := ys1 ++ ys2); auto.
    apply pointsto_iter_procact_merge; auto.
    exists ph1a, ph1b'. repeat split; vauto.
    exists pm1a, pm1b. repeat split; vauto.
Qed.
