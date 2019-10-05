Require Import HahnBase.
Require Import Heap.
Require Import List.
Require Import Permissions.
Require Import Prerequisites.
Require Import Process.
Require Import ProcessMap.
Require Import Setoid.
Require Import Statics.
Require Import Qcanon.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.

Set Implicit Arguments.


(** * Dynamics *)

(** This section discusses the dynamic behaviour of programs, which includes
    the denotational semantics of (Boolean) expressions and the small-step operational
    semantics of programs. In particular, we define two versions of the operational semantics;
    the first version is standard, and the second a ghost operational semantics that executes
    the operational semantics of process algebras alongside the standard operational semantics
    of programs. This second version thereby executes the abstract model alongside the concrete model.
    The soundness argument of the program logic provides a simulation between the two operational semantics. *)

Definition Store := Var -> Val.


(** ** Denotational semantics *)

(** The denotational semantics of (Boolean) expressions is defined in the standard way,
    and is also lifted to maps of expressions. *)

Open Scope Z_scope.

Fixpoint expr_denot (E : Expr)(s : Store) : Val :=
  match E with
    | Econst n => n
    | Evar x => s x
    | Eplus E1 E2 => expr_denot E1 s + expr_denot E2 s
  end.

Definition expr_denot_map {T} (f : T -> Expr)(s : Store) : T -> Val :=
  fun x : T => expr_denot (f x) s.

Close Scope Z_scope.

Fixpoint bexpr_denot (B : BoolExpr)(s : Store) : bool :=
  match B with
    | Bconst b => b
    | Bnot B' => negb (bexpr_denot B' s)
    | Band B1 B2 => (bexpr_denot B1 s) && (bexpr_denot B2 s)
    | Beq E1 E2 => if Z.eq_dec (expr_denot E1 s) (expr_denot E2 s) then true else false
  end.

(** Standard properties relating substitution to evaluation. *)

Lemma expr_denot_subst :
  forall E1 E2 x s,
  expr_denot (expr_subst x E1 E2) s =
  expr_denot E2 (update s x (expr_denot E1 s)).
Proof.
  intros E1 E2 x s.
  unfold update.
  induction E2; simpl; intuition. desf.
Qed.

Lemma bexpr_denot_subst :
  forall B E x s,
  bexpr_denot (bexpr_subst x E B) s =
  bexpr_denot B (update s x (expr_denot E s)).
Proof.
  induction B; intros E x s; simpl; intuition.
  by rewrite IHB.
  by rewrite IHB1, IHB2.
  by repeat rewrite expr_denot_subst.
Qed.

Lemma expr_denot_subst_map {T} :
  forall (f : T -> Expr) E x s,
  expr_denot_map (expr_subst_map x E f) s =
  expr_denot_map f (update s x (expr_denot E s)).
Proof.
  intros f E x s.
  extensionality y.
  apply expr_denot_subst.
Qed.

(** The following two lemmas relate the evaluation of (abstract) process expressions
    with the evaluation of (concrete) program expressions. *)

Lemma expr_denot_conv :
  forall (e : ProcExpr)(ps : ProcStore)(s : Store)(f : ProcVar -> Expr),
    (forall x : ProcVar, In x (pexpr_fv e) -> ps x = expr_denot (f x) s) ->
  expr_denot (pexpr_convert e f) s =
  pexpr_denot e ps.
Proof.
  induction e; intros ps s f H; vauto.
  (* [e] is of the form [PEvar x] *)
  - simpl pexpr_convert. rewrite <- H; auto.
    simpl. by left.
  (* [e] is of the form [PEplus e1 e2] *)
  - simpl pexpr_convert. simpl pexpr_denot.
    rewrite <- IHe1 with (s := s)(f := f); vauto.
    rewrite <- IHe2 with (s := s)(f := f); vauto.
    + intros x H1. apply H. simpl.
      apply in_app_iff. by right.
    + intros x H1. apply H. simpl.
      apply in_app_iff. by left.
Qed.

Lemma bexpr_denot_conv :
  forall (b : ProcBoolExpr)(ps : ProcStore)(s : Store)(f : ProcVar -> Expr),
    (forall x : ProcVar, In x (pbexpr_fv b) -> ps x = expr_denot (f x) s) ->
  bexpr_denot (pbexpr_convert b f) s =
  pbexpr_denot b ps.
Proof.
  induction b; intros ps s f H; vauto.
  (* [b] is of the form [PBnot b'] *)
  - simpls. rewrite <- IHb with (s := s)(f := f); vauto.
  (* [b] is of the form [PBand b1 b2] *)
  - simpls. rewrite <- IHb1 with (s := s)(f := f); vauto.
    rewrite <- IHb2 with (s := s)(f := f); vauto.
    + intros x H1. apply H.
      apply in_app_iff. by right.
    + intros x H1. apply H.
      apply in_app_iff. by left.
  (* [b] is of the form [PBeq e1 e2] *)
  - simpls. repeat rewrite expr_denot_conv with (ps := ps); vauto.
    + intros x H1. apply H.
      apply in_app_iff. by right.
    + intros x H1. apply H.
      apply in_app_iff. by left.
Qed.


(** *** Store agreement *)

(** Two stores _agreeing_ on a finite set of variables (where the finite set
    is represented by a list). *)

Definition store_agree (xs : list Var)(s1 s2 : Store) : Prop :=
  forall x : Var, In x xs -> s1 x = s2 x.

Lemma store_agree_split :
  forall xs1 xs2 s1 s2,
  store_agree (xs1 ++ xs2) s1 s2 ->
  store_agree xs1 s1 s2 /\ store_agree xs2 s1 s2.
Proof.
  intros xs1 xs2 s1 s2 H1.
  split; intros x H2.
  - apply H1. apply in_or_app. by left.
  - apply H1. apply in_or_app. by right.
Qed.

(** The evaluation of (Boolean) expressions only depends on the free variables in the expressions. *)

Lemma expr_agree :
  forall E s1 s2,
  store_agree (expr_fv E) s1 s2 ->
  expr_denot E s1 = expr_denot E s2.
Proof.
  induction E; intros s1 s2 H; simpls.
  - apply H. vauto.
  - apply store_agree_split in H. des.
    by rewrite IHE1 with s1 s2, IHE2 with s1 s2.
Qed.

Lemma bexpr_agree :
  forall B s1 s2,
  store_agree (bexpr_fv B) s1 s2 ->
  bexpr_denot B s1 = bexpr_denot B s2.
Proof.
  induction B; intros s1 s2 H; simpls.
  - by rewrite IHB with s1 s2.
  - apply store_agree_split in H.
    destruct H as (H1 & H2).
    by rewrite IHB1 with s1 s2, IHB2 with s1 s2.
  - apply store_agree_split in H.
    destruct H as (H1 & H2).
    by rewrite expr_agree with E1 s1 s2, expr_agree with E2 s1 s2.
Qed.

Lemma expr_map_agree {T} :
  forall (f : T -> Expr) s1 s2,
    (forall x, expr_map_fv f x -> s1 x = s2 x) ->
  expr_denot_map f s1 = expr_denot_map f s2.
Proof.
  intros f s1 s2 H1.
  extensionality t. apply expr_agree.
  red. intros x H2. apply H1.
  by exists t.
Qed.

(** Standard properties relating (Boolean) expression evaluation to store updates. *)

Lemma expr_denot_upd :
  forall E s x v,
  ~ In x (expr_fv E) ->
  expr_denot E (update s x v) = expr_denot E s.
Proof.
  intros E s x v H1.
  rewrite expr_agree with E s (update s x v); vauto.
  intros y H2. unfold update. desf.
Qed.

Lemma bexpr_denot_upd :
  forall B s x v,
  ~ In x (bexpr_fv B) ->
  bexpr_denot B (update s x v) = bexpr_denot B s.
Proof.
  intros B s x v H1.
  rewrite bexpr_agree with B s (update s x v); vauto.
  intros y H2. unfold update. desf.
Qed.


(** ** Shared memory accesses *)

(** The operation [cmd_acc C s] defines the set of heap locations that are
    _accessed_ by the program [C] in a single execution step, where [s] is used
    to evaluate all expressions referring to heap locations. Likewise, the operation
    [cmd_writes C s] determines the set of heap locations that are _written to_
    by [C] in a single execution step. Note that, rather than yielding a set of
    heap locations, both these operations are defined as predicates instead for
    later convenience. *)

Fixpoint cmd_acc {T} (C : Cmd T)(s : Store)(l : Loc) : Prop :=
  match C with
    | Cskip => False
    | Cseq C' _ => cmd_acc C' s l
    | Cass _ _ => False
    | Cread _ E
    | Cwrite E _ => l = expr_denot E s
    | Cite _ _ _
    | Cwhile _ _ => False
    | Cpar C1 C2 => cmd_acc C1 s l \/ cmd_acc C2 s l
    | Calloc _ _ => False
    | Cdispose E => l = expr_denot E s
    | Catomic _ => False
    | Cinatom C' => cmd_acc C' s l
    | Cproc _ _ xs f => exists x, In x xs /\ l = expr_denot (f x) s
    | Cact _ _ C' => False
    | Cinact _ C' => cmd_acc C' s l
    | Cendproc _ => False
  end.

Fixpoint cmd_writes {T} (C : Cmd T)(s : Store)(l : Loc) : Prop :=
  match C with
    | Cskip => False
    | Cseq C' _ => cmd_writes C' s l
    | Cass _ _
    | Cread _ _ => False
    | Cwrite E _ => l = expr_denot E s
    | Cite _ _ _
    | Cwhile _ _ => False
    | Cpar C1 C2 => cmd_writes C1 s l \/ cmd_writes C2 s l
    | Calloc _ _ => False
    | Cdispose E => l = expr_denot E s
    | Catomic _ => False
    | Cinatom C' => cmd_writes C' s l
    | Cproc _ _ _ _
    | Cact _ _ _ => False
    | Cinact _ C' => cmd_writes C' s l
    | Cendproc _ => False
  end.

(** All writes to shared memory are also shared-memory accesses. *)

Lemma cmd_writes_acc {T} :
  forall (C : Cmd T) s l,
  cmd_writes C s l -> cmd_acc C s l.
Proof.
  induction C; intros s l H; simpls; vauto.
  - by apply IHC1.
  - destruct H as [H | H].
    left. by apply IHC1.
    right. by apply IHC2.
  - by apply IHC.
  - by apply IHC.
Qed.

(** Other standard properties of shared-memory accesses. *)

Lemma cmd_acc_agree {T} :
  forall (C : Cmd T) s1 s2 l,
    (forall x, cmd_fv C x -> s1 x = s2 x) ->
  cmd_acc C s1 l = cmd_acc C s2 l.
Proof.
  induction C; intros s1 s2 l H; simpls; vauto.
  - rewrite IHC1 with (s2 := s2); auto.
  - rewrite expr_agree with (s2 := s2); auto.
    red. intros y H1. apply H. by right.
  - rewrite expr_agree with (s2 := s2); auto.
    red. intros y H1. apply H. by left.
  - rewrite IHC1 with (s2 := s2), IHC2 with (s2 := s2); auto.
  - rewrite expr_agree with (s2 := s2); auto.
  - rewrite IHC with (s2 := s2); auto.
  - apply f_equal. extensionality y.
    rewrite expr_agree with (s2 := s2); auto.
    red. intros z H1. apply H.
    right. by exists y.
  - rewrite IHC with (s2 := s2); auto.
Qed.

Lemma cmd_writes_agree {T} :
  forall (C : Cmd T) s1 s2 l,
    (forall x, cmd_fv C x -> s1 x = s2 x) ->
  cmd_writes C s1 l = cmd_writes C s2 l.
Proof.
  induction C; intros s1 s2 l H; simpls; vauto.
  - rewrite IHC1 with (s2 := s2); auto.
  - rewrite expr_agree with (s2 := s2); auto.
    red. ins. apply H. by left.
  - rewrite IHC1 with (s2 := s2), IHC2 with (s2 := s2); auto.
  - rewrite expr_agree with (s2 := s2); auto.
  - rewrite IHC with (s2 := s2); auto.
  - rewrite IHC with (s2 := s2); auto.
Qed.

Lemma cmd_acc_plain {T} :
  forall (C : Cmd T) s,
  cmd_acc (plain C) s = cmd_acc C s.
Proof.
  induction C; intros s; simpls; vauto.
  by rewrite IHC1, IHC2.
Qed.

Lemma cmd_writes_plain {T} :
  forall (C : Cmd T) s,
  cmd_writes (plain C) s = cmd_writes C s.
Proof.
  induction C; intros s; simpls; vauto.
  by rewrite IHC1, IHC2.
Qed.


(** ** Standard operational semantics *)

(** The standard small-step operational semantics of programs. Observe that the process-related
    commands are ignored and handled as if they were comments, since these are
    specification-only commands. Moreover, the transition rules for the parallel composition
    only allow a program to make a step if the other program is not locked. This allows to
    model atomic programs using a small-step semantics. *)

Inductive prog_sos : Heap -> Store -> PlainCmd ->
                     Heap -> Store -> PlainCmd -> Prop :=
  (* sequential - skip *)
  | psos_seq_skip h s C :
    prog_sos h s (Cseq Cskip C) h s C
  (* sequential - step *)
  | psos_seq_step h s C1 C2 h' s' C1' :
    prog_sos h s C1 h' s' C1' ->
    prog_sos h s (Cseq C1 C2) h' s' (Cseq C1' C2)
  (* assign *)
  | psos_assign h s x E :
    let v : Val := expr_denot E s in
    prog_sos h s (Cass x E) h (update s x v) Cskip
  (* heap read *)
  | psos_read h s x E v :
    h (expr_denot E s) = Some v ->
    prog_sos h s (Cread x E) h (update s x v) Cskip
  (* heap write *)
  | psos_write h s E1 E2 v :
    let l : Loc := expr_denot E1 s in
    let v' : Val := expr_denot E2 s in
    h l = Some v ->
    prog_sos h s (Cwrite E1 E2) (update h l (Some v')) s Cskip
  (* if-then-else - true branch *)
  | psos_ite_t h s B C1 C2 :
    bexpr_denot B s = true ->
    prog_sos h s (Cite B C1 C2) h s C1
  (* if-then-else, false branch *)
  | psos_ite_f h s B C1 C2 :
    bexpr_denot B s = false ->
    prog_sos h s (Cite B C1 C2) h s C2
  (* while loop *)
  | psos_while h s B C :
    prog_sos h s (Cwhile B C) h s (Cite B (Cseq C (Cwhile B C)) Cskip)
  (* heap alloc *)
  | psos_alloc h s x E l :
    let v : Val := expr_denot E s in
    h l = None ->
    prog_sos h s (Calloc x E) (update h l (Some v)) (update s x l) Cskip
  (* heap dispose *)
  | psos_dispose h s E :
    let l : Loc := expr_denot E s in
    prog_sos h s (Cdispose E) (update h l None) s Cskip
  (* atomic block - init *)
  | psos_atom h s C :
    prog_sos h s (Catomic C) h s (Cinatom C)
  (* atomic block - step *)
  | psos_inatom_step h s C h' s' C' :
    prog_sos h s C h' s' C' ->
    prog_sos h s (Cinatom C) h' s' (Cinatom C')
  (* atomic block - end *)
  | psos_inatom_end h s :
    prog_sos h s (Cinatom Cskip) h s Cskip
  (* parallel - left program *)
  | psos_par_l h s C1 C2 h' s' C1' :
    prog_sos h s C1 h' s' C1' ->
    ~ cmd_locked C2 ->
    prog_sos h s (Cpar C1 C2) h' s' (Cpar C1' C2)
  (* parallel - right program *)
  | psos_par_r h s C1 C2 h' s' C2' :
    prog_sos h s C2 h' s' C2' ->
    ~ cmd_locked C1 ->
    prog_sos h s (Cpar C1 C2) h' s' (Cpar C1 C2')
  (* parallel - done *)
  | psos_par_done h s :
    prog_sos h s (Cpar Cskip Cskip) h s Cskip
  (* process - init *)
  | psos_proc_init h s X p xs f :
    prog_sos h s (Cproc X p xs f) h s Cskip
  (* process - end *)
  | psos_proc_end h s X :
    prog_sos h s (Cendproc X) h s Cskip
  (* action block - init *)
  | psos_act h s X a C :
    prog_sos h s (Cact X a C) h s (Cinact PMnone C)
  (* action block - skip *)
  | psos_act_skip h s :
    prog_sos h s (Cinact PMnone Cskip) h s Cskip
  (* action block - step *)
  | psos_act_step h s C h' s' C' :
    prog_sos h s C h' s' C' ->
    prog_sos h s (Cinact PMnone C) h' s' (Cinact PMnone C').

Add Search Blacklist "prog_sos_ind".

(** Program basicality, program well-formedness and heap finiteness remain invariant
    during program execution. *)

Lemma prog_sos_basic_pres :
  forall C h s C' h' s',
  cmd_basic C -> prog_sos h s C h' s' C' -> cmd_basic C'.
Proof.
  induction C; intros h s C' h' s' H1 H2;
    inv H2; simpls; desf; intuition vauto.
  - by apply IHC1 in H8.
  - by apply IHC1 in H5.
  - by apply IHC2 in H5.
  - by apply IHC in H4.
Qed.

Lemma prog_sos_wf_pres :
  forall C h s C' h' s',
  cmd_wf C -> prog_sos h s C h' s' C' -> cmd_wf C'.
Proof.
  induction C; intros h s C' h' s' H1 H2;
    inv H2; simpls; desf; intuition vauto.
  - by apply IHC1 in H8.
  - by apply IHC1 in H5.
  - by apply IHC2 in H5.
  - by apply IHC in H4.
  - by apply prog_sos_basic_pres in H4.
Qed.

Lemma prog_sos_heap_finite :
  forall C h s C' h' s',
  prog_sos h s C h' s' C' ->
  heap_finite h ->
  heap_finite h'.
Proof.
  induction C; intros h s C' h' s' STEP FIN; inv STEP; vauto.
  (* sequential composition *)
  - by apply IHC1 in H6.
  (* heap writing *)
  - by apply heap_finite_upd.
  (* parallel - left *)
  - by apply IHC1 in H3.
  (* parallel - right *)
  - by apply IHC2 in H3.
  (* heap allocation *)
  - by apply heap_finite_upd.
  (* heap disposal *)
  - by apply heap_finite_upd.
  (* atomic programs *)
  - by apply IHC in H2.
  (* action programs *)
  - by apply IHC in H2.
Qed.

(** The sets of free- and modified variables do not grow during program execution. *)

Lemma prog_sos_fv_mod :
  forall C h s C' h' s',
  prog_sos h s C h' s' C' ->
    (forall x, cmd_fv C' x -> cmd_fv C x) /\
    (forall x, cmd_mod C' x -> cmd_mod C x) /\
    (forall x, ~ cmd_mod C x -> s x = s' x).
Proof.
  induction C; intros h s C' h' s' STEP; inv STEP; simpls.
  (* sequential composition *)
  - repeat split; intros x H; by right.
  - apply IHC1 in H6.
    destruct H6 as (F1 & F2 & F3).
    repeat split; intros x H.
    destruct H as [H | H].
    left. by apply F1. by right.
    destruct H as [H | H].
    left. by apply F2. by right.
    apply F3. intro H2.
    apply H. by left.
  (* assign *)
  - repeat split; intros y H; vauto.
    unfold update. intuition desf.
  (* heap reading *)
  - repeat split; intros y H; vauto.
    unfold update. intuition desf.
  (* if-then-else *)
  - repeat split; intros y H; vauto.
  - repeat split; intros y H; vauto.
  (* while-loops *)
  - repeat split; intros y H; vauto.
    destruct H as [|[|]]; vauto.
    destruct H as [|[|]]; vauto.
    destruct H as [[|]|]; vauto.
  (* parallel composition *)
  - apply IHC1 in H3. clear IHC1 IHC2.
    destruct H3 as (H1 & H2 & H3).
    repeat split; intros y H; vauto.
    destruct H as [H | H].
    left. by apply H1. by right.
    destruct H as [H | H].
    left. by apply H2. by right.
    apply H3. intro H4. apply H. by left.
  - apply IHC2 in H3. clear IHC1 IHC2.
    destruct H3 as (H1 & H2 & H3).
    repeat split; intros y H; vauto.
    destruct H as [H | H].
    by left. right. by apply H1.
    destruct H as [H | H].
    by left. right. by apply H2.
    apply H3. intro H4. apply H. by right.
  (* heap allocation *)
  - repeat split; intros y H; vauto.
    unfold update. intuition desf.
  (* atomic programs *)
  - apply IHC in H2. desf.
  (* action programs *)
  - repeat split; intros y H; vauto.
  - apply IHC in H2. desf.
Qed.

Lemma prog_sos_agree :
  forall C h s1 s2 C' h' s1' (phi : Var -> Prop),
    (forall x, cmd_fv C x -> phi x) ->
    (forall x, phi x -> s1 x = s2 x) ->
    prog_sos h s1 C h' s1' C' ->
  exists s2',
    (forall x, phi x -> s1' x = s2' x) /\
    prog_sos h s2 C h' s2' C'.
Proof.
  induction C; intros h s1 s2 C' h' s1' phi H1 H2 STEP;
    inv STEP; clear STEP; simpls; intuition vauto;
    unfold store_agree in *; try (exists s2; intuition vauto; fail).
  (* sequential composition *)
  - apply IHC1 with (s2 := s2)(phi := phi) in H8; vauto.
    destruct H8 as (s2' & H3 & STEP).
    exists s2'. intuition vauto.
    intros x H. apply H1. by left.
  (* assignment *)
  - exists (update s2 x (expr_denot E s2)).
    split; vauto. intros y H. unfold update.
    destruct (Z.eq_dec x y); auto. clarify.
    rewrite <- expr_agree with (s1 := s1); auto.
    unfold store_agree. intros x H'.
    apply H2, H1. by right.
  (* heap reading *)
  - rewrite expr_agree with (s2 := s2) in H8; vauto.
    exists (update s2 x v). split; vauto.
    intros y H3. unfold update.
    destruct (Z.eq_dec x y); auto.
    red. intros y H.
    apply H2, H1. by right.
  (* heap writing *)
  - subst l l0 v' v'0.
    exists s2. split; vauto.
    rewrite expr_agree with (s2 := s2) in H8; vauto.
    repeat rewrite expr_agree with (s1 := s1')(s2 := s2); vauto.
    red. ins. apply H2, H1. by right.
    red. ins. apply H2, H1. by left.
    red. ins. apply H2, H1. by left.
  (* if-then-else *)
  - exists s2. split; vauto. constructor.
    rewrite <- bexpr_agree with (s1 := s1'); auto.
    red. ins. apply H2, H1. by left.
  - exists s2. split; vauto. constructor.
    rewrite <- bexpr_agree with (s1 := s1'); auto.
    red. ins. apply H2, H1. by left.
  (* parallel composition *)
  - apply IHC1 with (s2 := s2)(phi := phi) in H5; vauto.
    destruct H5 as (s2' & H3 & H4).
    exists s2'. split; vauto.
    intros x H. apply H1. by left.
  - apply IHC2 with (s2 := s2)(phi := phi) in H5; vauto.
    destruct H5 as (s2' & H3 & H4).
    exists s2'. split; vauto.
    intros x H. apply H1. by right.
  (* heap allocation *)
  - subst v. rewrite expr_agree with (s2 := s2).
    exists (update s2 x l).
    split; vauto. intros y H3.
    unfold update. destruct (Z.eq_dec x y); auto.
    red. ins. apply H2, H1. by right.
  (* heap disposal *)
  - subst l l0. exists s2.
    split; vauto.
    rewrite expr_agree with (s2 := s2); vauto.
    red. ins. by apply H2, H1.
  (* atomic programs *)
  - apply IHC with (s2 := s2)(phi := phi) in H4; vauto.
    destruct H4 as (s2' & H4 & H5).
    exists s2'. intuition vauto.
  (* process-related steps *)
  - destruct m. exists s2. split; vauto.
  - apply IHC with (s2 := s2)(phi := phi) in H4; vauto.
    destruct H4 as (s2' & H4 & H5).
    exists s2'. destruct m.
    split; vauto.
Qed.

(** A program step always mutates the executed program; one does not end up in the
    same program after performing a computation step. *)

Lemma prog_sos_neg_C :
  forall C h s h' s',
  ~ prog_sos h s C h' s' C.
Proof.
  induction C; intros h s h' s' STEP; vauto; inv STEP; clear STEP.
  (* sequential composition *)
  - by apply cmd_neg_seq in H5.
  - by apply IHC1 in H5.
  (* if-then-else *)
  - by apply cmd_neg_ite_t in H6.
  - by apply cmd_neg_ite_f in H6.
  (* parallel composition *)
  - by apply IHC1 in H6.
  - by apply IHC2 in H6.
  (* atomic programs *)
  - by apply IHC in H5.
  (* action programs *)
  - by apply IHC in H5.
Qed.


(** ** Standard abort semantics *)

(** The abort semantics of programs formally defines the notion of a data-race,
    as well as memory safety (a program is _memory-safe_ if it does not access
    a memory location that has not been allocated). *)

Inductive prog_abort {T} : Heap -> Store -> Cmd T -> Prop :=
  (* heap read *)
  | pabort_read h s x E :
    h (expr_denot E s) = None ->
    prog_abort h s (Cread x E)
  (* heap write *)
  | pabort_write h s E1 E2 :
    h (expr_denot E1 s) = None ->
    prog_abort h s (Cwrite E1 E2)
  (* heap allocation *)
  | pabort_alloc h s x E :
    (~ exists l : Loc, h l = None) ->
    prog_abort h s (Calloc x E)
  (* heap disposal *)
  | pabort_dispose h s E :
    h (expr_denot E s) = None ->
    prog_abort h s (Cdispose E)
  (* parallel - left *)
  | pabort_par_l h s C1 C2 :
    prog_abort h s C1 ->
    ~ cmd_locked C2 ->
    prog_abort h s (Cpar C1 C2)
  (* parallel - right *)
  | pabort_par_r h s C1 C2 :
    prog_abort h s C2 ->
    ~ cmd_locked C1 ->
    prog_abort h s (Cpar C1 C2)
  (* parallel - deadlock *)
  | pabort_deadlock h s C1 C2 :
    cmd_locked C1 ->
    cmd_locked C2 ->
    prog_abort h s (Cpar C1 C2)
  (* action step *)
  | pabort_act h s m C :
    prog_abort h s C ->
    prog_abort h s (Cinact m C)
  (* sequential composition *)
  | pabort_seq h s C1 C2 :
    prog_abort h s C1 ->
    prog_abort h s (Cseq C1 C2)
  (* atomic programs *)
  | pabort_atom h s C :
    prog_abort h s C ->
    prog_abort h s (Cinatom C)
  (* data race - case 1 *)
  | pabort_race_l h s C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_writes C1 s) (cmd_acc C2 s) ->
    prog_abort h s (Cpar C1 C2)
  (* data race - case 2 *)
  | pabort_race_r h s C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_acc C1 s) (cmd_writes C2 s) ->
    prog_abort h s (Cpar C1 C2).

Add Search Blacklist "prog_abort_ind".

Lemma prog_abort_agree {T} :
  forall (C : Cmd T) h s1 s2,
    (forall x, cmd_fv C x -> s1 x = s2 x) ->
  prog_abort h s1 C ->
  prog_abort h s2 C.
Proof.
  induction C; intros h s1 s2 H1 ABORT; simpls; inv ABORT; clear ABORT.
  (* sequential composition *)
  - constructor. apply IHC1 with s1; vauto.
    ins. apply H1. by left.
  (* heap reading *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
    unfold store_agree. intros y H2.
    apply H1. by right.
  (* heap writing *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
    unfold store_agree. intros y H2.
    apply H1. by left.
  (* parallel - left *)
  - apply pabort_par_l; vauto.
    apply IHC1 with s1; auto.
  (* parallel - right *)
  - apply pabort_par_r; vauto.
    apply IHC2 with s1; auto.
  (* parallel - deadlock *)
  - by apply pabort_deadlock.
  (* data race - left *)
  - apply pabort_race_l; vauto.
    intro H3. apply H6.
    red. intros l F1 F2.
    rewrite cmd_writes_agree with (s4 := s2) in F1; auto.
    rewrite cmd_acc_agree with (s4 := s2) in F2; auto.
    by apply H3 with l.
  (* data race - right *)
  - apply pabort_race_r; vauto.
    intro H3. apply H6.
    red. intros l F1 F2.
    rewrite cmd_acc_agree with (s4 := s2) in F1; auto.
    rewrite cmd_writes_agree with (s4 := s2) in F2; auto.
    by apply H3 with l.
  (* heap allocation *)
  - by constructor.
  (* heap disposal *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
  (* atomic programs *)
  - constructor.
    apply IHC with s1; auto.
  (* action block *)
  - constructor.
    apply IHC with s1; auto.
Qed.

(** Progress of standard program execution: every configuration that does not abort
    can either make a computation step, or has already terminated. *)

Theorem prog_sos_progress :
  forall C h s,
  ~ prog_abort h s C ->
  C = Cskip \/ exists C' h' s', prog_sos h s C h' s' C'.
Proof.
  induction C; intros h s ABORT.
  (* empty programs *)
  - by left.
  (* sequential composition *)
  - cut (C1 = Cskip \/ ~ C1 = Cskip); [|apply classic].
    intro H. right.
    destruct H as [H1 | H1].
    (* left program [C1] is empty *)
    + clarify. exists C2, h, s. vauto.
    (* left program [C1] is not empty *)
    + cut (~ prog_abort h s C1).
      * intro H2. apply IHC1 in H2.
        destruct H2 as [H2 | H2]; vauto.
        destruct H2 as (C1' & h' & s' & STEP).
        exists (Cseq C1' C2), h', s'. vauto.
      * intro H2. apply ABORT. vauto.
  (* assignment *)
  - right. exists Cskip, h, (update s x (expr_denot E s)).
    constructor.
  (* heap reading *)
  - right. cut (exists v, h (expr_denot E s) = Some v).
    + intro H1. destruct H1 as (v & H1).
      exists Cskip, h, (update s x v). vauto.
    + rewrite <- option_not_none.
      intro H1. apply ABORT. vauto.
  (* heap writing *)
  - right. cut (exists v, h (expr_denot E1 s) = Some v).
    + intro H1. destruct H1 as (v & H1).
      exists Cskip, (update h (expr_denot E1 s) (Some (expr_denot E2 s))), s.
      by apply psos_write with v.
    + rewrite <- option_not_none.
      intro H. apply ABORT. vauto.
  (* if-then-else *)
  - right. cut (bexpr_denot B s = true \/ bexpr_denot B s = false).
    + intro H1. destruct H1 as [H1 | H1].
      exists C1, h, s. vauto.
      exists C2, h, s. vauto.
    + rewrite <- Bool.not_true_iff_false.
      apply classic.
  (* while-loops *)
  - right. exists (Cite B (Cseq C (Cwhile B C)) Cskip), h, s. vauto.
  (* parallel composition *)
  - right.
    cut ((~ cmd_locked C2 /\ exists C1' h' s', prog_sos h s C1 h' s' C1') \/
         (~ cmd_locked C1 /\ exists C2' h' s', prog_sos h s C2 h' s' C2') \/
          C1 = Cskip /\ C2 = Cskip).
    (* progress for all three cases in the cut *)
    + intro H. destruct H as [H | [H | H]].
      (* [C1] makes a step *)
      * destruct H as (H & C1' & h' & s' & STEP).
        exists (Cpar C1' C2), h', s'. vauto.
      (* [C2] makes a step *)
      * destruct H as (H & C2' & h' & s' & STEP).
        exists (Cpar C1 C2'), h', s'. vauto.
      (* [C1] and [C2] have both terminated *)
      * destruct H as (H1 & H2). clarify.
        exists Cskip, h, s. vauto.
    (* one of the three cases in the cut must hold *)
    + cut (C1 = Cskip \/ ~ C1 = Cskip); [|apply classic].
      cut (C2 = Cskip \/ ~ C2 = Cskip); [|apply classic].
      intros H1 H2. desf.
      (* [C1] and [C2] have both terminated *)
      * by repeat right.
      (* [C1] has terminated, [C2] has not *)
      * right. left. split.
        intro H2. inv H2.
        apply imply_and_or with (C2 = Cskip); vauto.
        apply IHC2. intro ABORT'.
        apply ABORT. vauto.
      (* [C2] has terminated, [C1] has not *)
      * left. split. intro H3. inv H3.
        apply imply_and_or with (C1 = Cskip); vauto.
        apply IHC1. intro ABORT'.
        apply ABORT. vauto.
      (* [C1] and [C2] have both not terminated *)
      * cut (cmd_locked C1 \/ ~ cmd_locked C1); [|apply classic].
        intro H3. destruct H3 as [H3 | H3].
        (* [C1] is locked *)
        ** assert (H : ~ cmd_locked C2). {
           intro H4. apply ABORT. vauto. }
           left. split. auto.
           apply imply_and_or with (C1 = Cskip); vauto.
           apply IHC1. intro ABORT'.
           apply ABORT. vauto.
        (* [C1] is not locked *)
        ** right. left. split. auto.
           apply imply_and_or with (C2 = Cskip); vauto.
           apply IHC2. intro ABORT'.
           apply ABORT. vauto.
  (* heap allocation *)
  - right. cut (exists l, h l = None).
    + intro H. destruct H as (l & H).
      exists Cskip, (update h l (Some (expr_denot E s))), (update s x l). vauto.
    + apply NNPP. intro H. apply ABORT. vauto.
  (* heap disposal *)
  - right.
    exists Cskip, (update h (expr_denot E s) None), s. vauto.
  (* atomic block - init *)
  - right. exists (Cinatom C), h, s. vauto.
  (* atomic block - step *)
  - right. cut (C = Cskip \/ ~ C = Cskip); [|apply classic].
    intro H. destruct H as [H | H].
    (* [C] has terminated *)
    + clarify. exists Cskip, h, s. constructor.
    (* [C] has not terminated *)
    + cut (~ prog_abort h s C).
      * intro H1. apply IHC in H1.
        destruct H1 as [H1 | H1]; vauto.
        destruct H1 as (C' & h' & s' & STEP).
        exists (Cinatom C'), h', s'. vauto.
      * intro H1. apply ABORT. vauto.
  (* process - init *)
  - right. exists Cskip, h, s. vauto.
  (* action - init *)
  - right. exists (Cinact PMnone C), h, s. vauto.
  (* action - step *)
  - right. cut (C = Cskip \/ ~ C = Cskip); [|apply classic].
    intro H. destruct H as [H | H].
    (* [C] has terminated *)
    + clarify. exists Cskip, h, s.
      destruct m. vauto.
    (* [C] has not terminated *)
    + cut (~ prog_abort h s C).
      * intro H1. apply IHC in H1.
        destruct H1 as [H1 | H1]; vauto.
        destruct H1 as (C' & h' & s' & STEP).
        exists (Cinact m C'), h', s'.
        destruct m. vauto.
      * intro H1. apply ABORT. vauto.
  (* process - end *)
  - right. exists Cskip, h, s. vauto.
Qed.


(** ** Ghost operational semantics *)

(** The small-step ghost operational semantics of programs, which executes the
    standard operational semantics of programs alongside the operational semantics
    of processes (i.e. the ghost components) from Process.v. The interaction between the program- and
    process operational semantics is described in the program with the process-related
    commands (which were ignored in the standard operational semantics). *)

(** To deal with process-related commands, the configurations in the ghost semantics
    have two extra components compared to the standard semantics, namely: a process map
    (of type [ProcMap]) containing information regarding all activated processes; and an extra store (of type [Store]),
    which we refer to as the _ghost store_, as it is used to give an interpretation for
    all variables that contain information about ghost components. *)

(** Moreover, the ghost semantics also maintains some extra runtime information for every
    activated action (i.e. programs of the form [Cinact]), specified as _metadata_ of type [GhostMetadata]. To clarify,
    every action block that becomes active during program execution maintains the following information:
    - The identifier of the process map entry (of type [ProcID]) in whose context the action is being executed;
    - The label of the corresponding action being executed (of type [ActLabel]); and
    - A copy (or snapshot) of the heap, made when the action block became active. *)

Definition GhostMetadata : Type := ProcID * ActLabel * Heap.
Definition GhostCmd : Type := Cmd GhostMetadata.

Inductive ghost_sos : Heap -> ProcMap -> Store -> Store -> GhostCmd ->
                      Heap -> ProcMap -> Store -> Store -> GhostCmd -> Prop :=
  (* sequential - skip *)
  | gsos_seq_skip h pm s g C :
    ghost_sos h pm s g (Cseq Cskip C) h pm s g C
  (* sequential - step *)
  | gsos_seq_step h pm s g C1 C2 h' pm' s' g' C1' :
    ghost_sos h pm s g C1 h' pm' s' g' C1' ->
    ghost_sos h pm s g (Cseq C1 C2) h' pm' s' g' (Cseq C1' C2)
  (* assign *)
  | gsos_assign h pm s g x E :
    let v := expr_denot E s in
    ghost_sos h pm s g (Cass x E) h pm (update s x v) g Cskip
  (* heap read *)
  | gsos_read h pm s g x E v :
    h (expr_denot E s) = Some v ->
    ghost_sos h pm s g (Cread x E) h pm (update s x v) g Cskip
  (* heap write *)
  | gsos_write h pm s g E1 E2 v :
    let l := expr_denot E1 s in
    let v' := expr_denot E2 s in
    h l = Some v ->
    ghost_sos h pm s g (Cwrite E1 E2) (update h l (Some v')) pm s g Cskip
  (* if-then-else - true branch *)
  | gsos_ite_t h pm s g B C1 C2 :
    bexpr_denot B s = true ->
    ghost_sos h pm s g (Cite B C1 C2) h pm s g C1
  (* if-then-else - false branch *)
  | gsos_ite_f h pm s g B C1 C2 :
    bexpr_denot B s = false ->
    ghost_sos h pm s g (Cite B C1 C2) h pm s g C2
  (* while loop *)
  | gsos_while h pm s g B C :
    ghost_sos h pm s g (Cwhile B C) h pm s g (Cite B (Cseq C (Cwhile B C)) Cskip)
  (* heap alloc *)
  | gsos_alloc h pm s g x E l :
    let v : Val := expr_denot E s in
    h l = None ->
    ghost_sos h pm s g (Calloc x E) (update h l (Some v)) pm (update s x l) g Cskip
  (* heap dispose *)
  | gsos_dispose h pm s g E :
    let l : Loc := expr_denot E s in
    ghost_sos h pm s g (Cdispose E) (update h l None) pm s g Cskip
  (* atomic block - init *)
  | gsos_atom h pm s g C :
    ghost_sos h pm s g (Catomic C) h pm s g (Cinatom C)
  (* atomic block - step *)
  | gsos_inatom_step h pm s g C h' pm' s' g' C' :
    ghost_sos h pm s g C h' pm' s' g' C' ->
    ghost_sos h pm s g (Cinatom C) h' pm' s' g' (Cinatom C')
  (* atomic block - end *)
  | gsos_inatom_end h pm s g :
    ghost_sos h pm s g (Cinatom Cskip) h pm s g Cskip
  (* parallel - left *)
  | gsos_par_l h pm s g C1 C2 h' pm' s' g' C1' :
    ghost_sos h pm s g C1 h' pm' s' g' C1' ->
    ~ cmd_locked C2 ->
    ghost_sos h pm s g (Cpar C1 C2) h' pm' s' g' (Cpar C1' C2)
  (* parallel - right *)
  | gsos_par_r h pm s g C1 C2 h' pm' s' g' C2' :
    ghost_sos h pm s g C2 h' pm' s' g' C2' ->
    ~ cmd_locked C1 ->
    ghost_sos h pm s g (Cpar C1 C2) h' pm' s' g' (Cpar C1 C2')
  (* parallel - skip *)
  | gsos_par_done h pm s g :
    ghost_sos h pm s g (Cpar Cskip Cskip) h pm s g Cskip
  (* process - init *)
  | gsos_proc_init h pm s g x p xs f pid :
    pm pid = PMfree ->
    let P : Proc := body p in
    let f' := expr_denot_map f s in
    ghost_sos h pm s g (Cproc x p xs f) h (update pm pid (PMelem perm_full p P xs f')) s (update g x pid) Cskip
  (* process - end *)
  | gsos_proc_end h pm s g x p P xs f :
    let pid : ProcID := g x in
    pmv_eq (pm pid) (PMelem perm_full p P xs f) ->
    proc_term P ->
    ghost_sos h pm s g (Cendproc x) h (update pm pid PMfree) s g Cskip
  (* action - init *)
  | gsos_act h pm s g x a C :
    ghost_sos h pm s g (Cact x a C) h pm s g (Cinact (g x, a, h) C)
  (* action - end *)
  | gsos_act_skip h pm s g pid a hs q p P P' xs f ps1 ps2 :
    pmv_eq (pm pid) (PMelem q p P xs f) ->
      (forall x, In x xs -> hs (f x) = Some (ps1 x)) ->
      (forall x, In x xs -> h (f x) = Some (ps2 x)) ->
    proc_sos P ps1 a P' ps2 ->
    let pm' := update pm pid (PMelem q p P' xs f) in
    ghost_sos h pm s g (Cinact (pid, a, hs) Cskip) h pm' s g Cskip
  (* action - step *)
  | gsos_act_step h pm s g m C h' pm' s' g' C' :
    ghost_sos h pm s g C h' pm' s' g' C' ->
    ghost_sos h pm s g (Cinact m C) h' pm' s' g' (Cinact m C').

Add Search Blacklist "ghost_sos_ind".

(** The reduction rules of the standard operational semantics are embedded in the
    reduction rules of the ghost operational semantics. *)

Theorem ghost_sos_sim :
  forall C h pm s g C' h' pm' s' g',
  ghost_sos h pm s g C h' pm' s' g' C' ->
  prog_sos h s (plain C) h' s' (plain C').
Proof.
  induction C; intros h pm s g C' h' pm' s' g' STEP;
    simpls; inv STEP; clear STEP; simpls; vauto.
  (* sequential programs *)
  - constructor. by apply IHC1 in H10.
  (* parallel programs *)
  - constructor. by apply IHC1 in H5.
    by rewrite cmd_locked_plain.
  - constructor. by apply IHC2 in H5.
    by rewrite cmd_locked_plain.
  (* atomic programs *)
  - constructor. by apply IHC in H4.
  (* action programs *)
  - constructor. by apply IHC in H10.
Qed.

(** The ghost operational semantics can mimick the steps of the standard operational
    semantics for every basic program. *)

Theorem prog_sos_basic_sim :
  forall C h pm s g C' h' s',
  cmd_basic C ->
  prog_sos h s (plain C) h' s' C' ->
  exists C'', ghost_sos h pm s g C h' pm s' g C'' /\ C' = plain C''.
Proof.
  induction C; intros h pm s g C' h' s' H1 STEP; simpls;
    inv STEP; simpls; vauto;
    try (by exists Cskip; vauto).
  (* sequential composition - left program is empty *)
  - symmetry in H3. apply plain_skip in H3. clarify.
    exists C2. vauto.
  (* sequential composition - left program not empty *)
  - apply IHC1 with (pm := pm)(g := g) in H7; [|intuition].
    destruct H7 as (C1'' & H7 & H2).
    exists (Cseq C1'' C2). vauto.
  (* if-then-else - true branch *)
  - exists C1. vauto.
  (* if-then-else - false branch *)
  - exists C2. vauto.
  (* while-loop *)
  - exists (Cite B (Cseq C (Cwhile B C)) Cskip). vauto.
  (* parallel - step in left program *)
  - apply IHC1 with (pm := pm)(g := g) in H4; [|intuition].
    destruct H4 as (C1'' & H4 & H5).
    exists (Cpar C1'' C2). intuition vauto.
    apply gsos_par_l; auto. intro H5.
    apply H8. by rewrite cmd_locked_plain.
  (* parallel - step in right program *)
  - apply IHC2 with (pm := pm)(g := g) in H4; [|intuition].
    destruct H4 as (C2'' & H4 & H5).
    exists (Cpar C1 C2''). intuition vauto.
    apply gsos_par_r; auto. intro H5.
    apply H8. by rewrite cmd_locked_plain.
  (* parallel - both programs empty *)
  - symmetry in H3, H4. apply plain_skip in H3.
    apply plain_skip in H4. clarify.
    exists Cskip. intuition vauto.
  (* atomic programs - initialise *)
  - exists (Cinatom C). vauto.
  (* atomic programs - step *)
  - apply IHC with (pm := pm)(g := g) in H3; vauto.
    destruct H3 as (C'' & H3 & H4). clarify.
    exists (Cinatom C''). vauto.
  (* atomic programs - finish *)
  - exists Cskip. split; vauto.
    symmetry in H3. apply plain_skip in H3. clarify. vauto.
Qed.

(** Program basicality, program well-formedness and process map finiteness remain
    invariant during ghost program execution. *)

Lemma ghost_sos_basic_pres :
  forall C h pm s g C' h' pm' s' g',
  ghost_sos h pm s g C h' pm' s' g' C' ->
  cmd_basic C ->
  cmd_basic C'.
Proof.
  induction C; intros h pm s g C' h' pm' s' g' STEP H1;
    inv STEP; clear STEP; simpls; try (intuition vauto; fail).
  (* sequential composition *)
  - destruct H1 as (H1 & H2).
    split; auto. by apply IHC1 in H11.
  (* parallel composition - left *)
  - destruct H1 as (H1 & H2 & H3).
    repeat split; auto.
    + by apply IHC1 in H6.
    + intros (H4 & H5). apply H3. intuition.
  (* parallel composition - right *)
  - destruct H1 as (H1 & H2 & H3).
    repeat split; auto.
    + by apply IHC2 in H6.
    + intros (H4 & H5). apply H3. intuition.
  (* atomic programs *)
  - apply IHC in H5; vauto.
Qed.

Lemma ghost_sos_wf_pres :
  forall C h pm s g C' h' pm' s' g',
  ghost_sos h pm s g C h' pm' s' g' C' ->
  cmd_wf C ->
  cmd_wf C'.
Proof.
  induction C; intros h pm s g C' h' pm' s' g' STEP H1;
    inv STEP; clear STEP; simpls; try (intuition vauto; fail).
  (* sequential composition *)
  - destruct H1 as (H1 & H2).
    split; auto. by apply IHC1 in H11.
  (* parallel composition - left *)
  - destruct H1 as (H1 & H2 & H3).
    repeat split; auto.
    + by apply IHC1 in H6.
    + intros (H4 & H5). apply H3. intuition.
  (* parallel composition - right *)
  - destruct H1 as (H1 & H2 & H3).
    repeat split; auto.
    + by apply IHC2 in H6.
    + intros (H4 & H5). apply H3. intuition.
  (* atomic programs *)
  - by apply IHC in H5.
  (* atomic programs *)
  - by apply ghost_sos_basic_pres in H11.
Qed.

Lemma ghost_sos_procmap_finite :
  forall C h pm s g C' h' pm' s' g',
  ghost_sos h pm s g C h' pm' s' g' C' ->
  procmap_finite pm ->
  procmap_finite pm'.
Proof.
  induction C; intros h pm s g C' h' pm' s' g' STEP FIN; inv STEP; vauto.
  (* sequential composition *)
  - by apply IHC1 in H10.
  (* parallel - left *)
  - by apply IHC1 in H5.
  (* parallel - right *)
  - by apply IHC2 in H5.
  (* heap allocation *)
  - by apply IHC in H4.
  (* atomic programs *)
  - by apply procmap_finite_upd.
  (* action - end *)
  - subst pm'0. by apply procmap_finite_upd.
  (* action - computation step *)
  - by apply IHC in H10.
  (* process - end *)
  - by apply procmap_finite_upd.
Qed.

(** The ghost semantics can simulate computation steps made with bisimilar process maps. *)

Lemma ghost_sos_procmap_eq :
  forall C h pm1 pm2 s g C' h' pm1' s' g',
    procmap_eq pm1 pm2 ->
    ghost_sos h pm1 s g C h' pm1' s' g' C' ->
  exists pm2',
    ghost_sos h pm2 s g C h' pm2' s' g' C' /\
    procmap_eq pm1' pm2'.
Proof.
  induction C; intros h pm1 pm2 s g C' h' pm1' s' g' H1 STEP;
    inv STEP; clear STEP; simpls;
    try (exists pm2; intuition constructor; auto; fail).
  (* sequential composition *)
  - apply IHC1 with (pm2 := pm2) in H11; auto.
    destruct H11 as (pm2' & H2 & H3).
    exists pm2'. intuition by constructor.
  (* heap writing *)
  - exists pm2. split; auto.
    apply gsos_write with v. auto.
  (* parallel - left *)
  - apply IHC1 with (pm2 := pm2) in H6; auto.
    destruct H6 as (pm2' & H2 & H3).
    exists pm2'. split; vauto.
  (* parallel - right *)
  - apply IHC2 with (pm2 := pm2) in H6; auto.
    destruct H6 as (pm2' & H2 & H3).
    exists pm2'. split; vauto.
  (* atomic *)
  - apply IHC with (pm2 := pm2) in H5; auto.
    destruct H5 as (pm2' & H2 & H3).
    exists pm2'. split; vauto.
  (* process - init *)
  - exists (update pm2 pid (PMelem perm_full p P xs f')).
    split. constructor; auto.
    by apply procmap_eq_free with pm1.
    by rewrite H1.
  (* action - end *)
  - subst pm'.
    exists (update pm2 pid (PMelem q p P' xs f)).
    split; vauto.
    + apply gsos_act_skip with P ps1 ps2; auto.
      red in H1. by rewrite <- H1.
    + intro pid'. unfold update. desf.
  (* action - step *)
  - apply IHC with (pm2 := pm2) in H11; auto.
    destruct H11 as (pm2' & H2 & H3).
    exists pm2'. split; vauto.
  (* process - end *)
  - rename pid0 into pid'.
    exists (update pm2 pid' PMfree). split; vauto.
    + apply gsos_proc_end with p P xs f; vauto.
      subst pid'. rewrite <- H0. symmetry. by apply H1.
    + intro pid''. unfold update. desf.
Qed.

(** The sets of free- and modified variables do not grow during program ghost execution. *)

Lemma ghost_sos_fv_mod_g :
  forall C h pm s g C' h' pm' s' g' x,
  ghost_sos h pm s g C h' pm' s' g' C' ->
  ~ cmd_mod C x -> g x = g' x.
Proof.
  induction C; intros h pm s g C' h' pm' s' g' y STEP H2; inv STEP; simpls.
  (* sequential composition *)
  - apply IHC1 with (x := y) in H11; vauto.
    intro. apply H2. by left.
  (* parallel composition *)
  - apply IHC1 with (x := y) in H6. vauto.
    intro. apply H2. by left.
  - apply IHC2 with (x := y) in H6; vauto.
    intro. apply H2. by right.
  (* atomic program *)
  - apply IHC with (x := y) in H5; vauto.
  (* process - init *)
  - intuition vauto. unfold update. desf.
  (* action - step *)
  - apply IHC with (x := y) in H11; desf.
Qed.

Lemma ghost_sos_fv_mod :
  forall C h pm s g C' h' pm' s' g',
  ghost_sos h pm s g C h' pm' s' g' C' ->
    (forall x, cmd_fv C' x -> cmd_fv C x) /\
    (forall x, cmd_mod C' x -> cmd_mod C x) /\
    (forall x, ~ cmd_mod C x -> s x = s' x) /\
    (forall x, ~ cmd_mod C x -> g x = g' x).
Proof.
  intros C h pm s g C' h' pm' s' g' STEP.
  generalize STEP. intro STEP'.
  apply ghost_sos_sim, prog_sos_fv_mod in STEP.
  repeat rewrite <- cmd_fv_plain in STEP.
  repeat rewrite <- cmd_mod_plain in STEP.
  destruct STEP as (F1 & F2 & F3).
  repeat split; vauto. intros x H.
  apply ghost_sos_fv_mod_g with (x := x) in STEP'; vauto.
Qed.

Lemma ghost_sos_agree :
  forall C h pm s1 s2 g C' h' pm' s1' g' (phi : Var -> Prop),
    (forall x, cmd_fv C x -> phi x) ->
    (forall x, phi x -> s1 x = s2 x) ->
    ghost_sos h pm s1 g C h' pm' s1' g' C' ->
  exists s2',
    (forall x, phi x -> s1' x = s2' x) /\
    ghost_sos h pm s2 g C h' pm' s2' g' C'.
Proof.
  induction C; intros h pm s1 s2 g C' h' pm' s1' g' phi H1 H2 STEP;
    inv STEP; clear STEP; simpls;
    try (exists s2; intuition vauto; fail).
  (* sequential composition *)
  - apply IHC1 with (s2 := s2)(phi := phi) in H12; auto.
    destruct H12 as (s2' & H3 & H4).
    exists s2'. split; vauto.
  (* assignment *)
  - exists (update s2 x (expr_denot E s2)).
    split; vauto. intros y H3.
    unfold update.
    destruct (Z.eq_dec x y); auto. clarify.
    rewrite <- expr_agree with (s1 := s1); auto.
    red. intros x H4. apply H2, H1. by right.
  (* heap reading *)
  - rewrite expr_agree with (s2 := s2) in H12; vauto.
    exists (update s2 x v). split; vauto.
    intros y H3. unfold update.
    destruct (Z.eq_dec x y); vauto.
    by apply H2. red. intros y H4.
    apply H2, H1. by right.
  (* heap writing *)
  - subst l l0 v' v'0.
    exists s2. split; vauto.
    rewrite expr_agree with (s2 := s2) in H12; vauto.
    repeat rewrite expr_agree with (s1 := s1')(s2 := s2); vauto.
    red. ins. apply H2, H1. by right.
    red. ins. apply H2, H1. by left.
    red. ins. apply H2, H1. by left.
  (* if-then-else *)
  - exists s2. split; vauto. constructor.
    rewrite <- bexpr_agree with (s1 := s1'); auto.
    red. ins. apply H2, H1. by left.
  - exists s2. split; vauto. constructor.
    rewrite <- bexpr_agree with (s1 := s1'); auto.
    red. ins. apply H2, H1. by left.
  (* parallel composition *)
  - apply IHC1 with (s2 := s2)(phi := phi) in H7; vauto.
    destruct H7 as (s2' & H3 & H4).
    exists s2'. split; vauto.
    intros x H3. apply H1. by left.
  - apply IHC2 with (s2 := s2)(phi := phi) in H7; vauto.
    destruct H7 as (s2' & H3 & H4).
    exists s2'. split; vauto.
    intros x H3. apply H1. by right.
  (* heap allocation *)
  - subst v. rewrite expr_agree with (s2 := s2).
    exists (update s2 x l). split; vauto.
    intros y H3. unfold update.
    destruct (Z.eq_dec x y); vauto.
    by apply H2. red. intros y H3.
    apply H2, H1. by right.
  (* heap disposal *)
  - subst l l0. exists s2. split; vauto.
    rewrite expr_agree with (s2 := s2); vauto.
    red. ins. by apply H2, H1.
  (* atomic programs *)
  - apply IHC with (s2 := s2)(phi := phi) in H6; vauto.
    destruct H6 as (s2' & H3 & H4).
    exists s2'. split; vauto.
  (* process - init *)
  - subst f' f'0. exists s2. split; vauto.
    rewrite expr_map_agree with (s3 := s2); vauto.
    intros y H4. apply H2, H1. right.
    destruct H4 as (z & H4). by exists z.
  (* action - step *)
  - apply IHC with (s2 := s2)(phi := phi) in H12; vauto.
    destruct H12 as (s2' & H3 & H4).
    exists s2'. split; vauto.
Qed.

Lemma ghost_sos_agree_g :
  forall C h pm s g1 g2 C' h' pm' s' g1' (phi : Var -> Prop),
    (forall x, cmd_fv C x -> phi x) ->
    (forall x, phi x -> g1 x = g2 x) ->
    ghost_sos h pm s g1 C h' pm' s' g1' C' ->
  exists g2',
    (forall x, phi x -> g1' x = g2' x) /\
    ghost_sos h pm s g2 C h' pm' s' g2' C'.
Proof.
  induction C; intros h pm s g1 g2 C' h' pm' s' g1' phi H1 H2 STEP;
    inv STEP; clear STEP; simpls;
    try (exists g2; intuition vauto; fail).
  (* sequential composition *)
  - apply IHC1 with (g2 := g2)(phi := phi) in H12; auto.
    destruct H12 as (g2' & H3 & H4).
    exists g2'. split; vauto.
  (* parallel composition *)
  - apply IHC1 with (g2 := g2)(phi := phi) in H7; vauto.
    destruct H7 as (g2' & H3 & H4).
    exists g2'. split; vauto.
    intros x H. apply H1. by left.
  - apply IHC2 with (g2 := g2)(phi := phi) in H7; vauto.
    destruct H7 as (g2' & H3 & H4).
    exists g2'. split; vauto.
    intros x H. apply H1. by right.
  (* atomic programs *)
  - apply IHC with (g2 := g2)(phi := phi) in H6; vauto.
    destruct H6 as (g2' & H3 & H4).
    exists g2'. intuition vauto.
  (* process - init *)
  - exists (update g2 x pid).
    split; vauto. intros y H3. unfold update.
    destruct (Z.eq_dec x y); auto.
  (* action - init *)
  - exists g2. split; vauto.
    rewrite H2 in *; vauto; apply H1; vauto.
  (* action - step *)
  - apply IHC with (g2 := g2)(phi := phi) in H12; vauto.
    destruct H12 as (g2' & H3 & H4).
    exists g2'. intuition vauto.
  (* process - end *)
  - subst pid pid0.
    exists g2. split; vauto.
    rewrite H2 in *; vauto; apply H1; auto.
Qed.

(* Note: needed for the proof of [safe_agree]. *)
Lemma ghost_sos_agree_sim :
  forall C h pm s1 s2 g C' h' pm' s1' s2' g',
    (forall x, cmd_fv C x -> s1 x = s2 x) ->
    (forall x, cmd_fv C x -> s1' x = s2' x) ->
  prog_sos h s1 (plain C) h' s1' (plain C') ->
  ghost_sos h pm s2 g C h' pm' s2' g' C' ->
  ghost_sos h pm s1 g C h' pm' s1' g' C'.
Proof.
  induction C; intros h pm s1 s2 g C' h' pm' s1' s2' g' F1 F2 STEP GSTEP;
    inv STEP; clear STEP; inv GSTEP; clear GSTEP; simpls;
    try (desf; intuition vauto; fail).
  (* sequential composition *)
  - symmetry in H2. apply plain_skip in H2.
    clarify. inv H12.
  - inv H5.
  - rename C1'0 into C1''.
    apply IHC1 with (s1 := s1)(s1' := s1') in H12; vauto.
    intros x H. apply F1. by left.
    intros x H. apply F2. by left.
  (* if-then-else *)
  - constructor. rewrite bexpr_agree with (s2 := s2'); auto.
    red. intros x H. apply F1. by left.
  - constructor. rewrite bexpr_agree with (s2 := s2'); auto.
    red. intros x H. apply F1. by left.
  (* parallel composition *)
  - rename C1'0 into C1''. apply gsos_par_l; auto.
    apply IHC1 with s2 s2'; vauto.
    intros x H. apply F1. by left.
    intros x H. apply F2. by left.
  - simpls. vauto. by apply prog_sos_neg_C in H6.
  - simpls. vauto. by apply prog_sos_neg_C in H6.
  - apply gsos_par_r; auto.
    apply IHC2 with s2 s2'; vauto.
    intros x H. apply F1. by right.
    intros x H. apply F2. by right.
  (* heap allocation *)
  - subst v0. clear H6.
    assert (H1 : update s1 x l x = update s2 x l0 x). {
    apply F2. by left. }
    unfold update in H1.
    destruct (Z.eq_dec x x) as [_|H2]; vauto.
    rewrite <- expr_agree with (s1 := s1).
    by constructor. red.
    intros y H. apply F1. by right.
  (* atomic programs *)
  - rename C'1 into C'. constructor.
    apply IHC with s2 s2'; vauto.
  (* process - init *)
  - subst f' f'0. clear H4.
    rewrite <- expr_map_agree with (s1 := s1'); vauto.
    intros y H. apply F2. right.
    destruct H as (z & H). by exists z.
  (* action program - step *)
  - rename C'1 into C'. constructor.
    apply IHC with s2 s2'; vauto.
Qed.

(** Ghost steps in basic programs do not affect the ghost components [pm] and [g]. *)

Lemma ghost_sos_basic_ghostdata_pres :
  forall C h pm s g C' h' pm' s' g',
  cmd_basic C ->
  ghost_sos h pm s g C h' pm' s' g' C' ->
  pm = pm' /\ g = g'.
Proof.
  induction C; intros h pm s g C' h' pm' s' g' BASIC STEP; vauto; inv STEP; vauto.
  (* sequential composition *)
  - apply IHC1 in H10; intuition vauto.
    simpl in BASIC. desf.
  (* parallel composition - step in left program *)
  - apply IHC1 in H5; intuition vauto.
    simpl in BASIC. desf.
  (* parallel composition - step in right program *)
  - apply IHC2 in H5; intuition vauto.
    simpl in BASIC. desf.
  (* atomic programs *)
  - apply IHC in H4; vauto.
Qed.


(** ** Ghost abort semantics *)

(** The ghost abort semantics defines the notions of data-races and memory-safety,
    likewise to [prog_abort], as well as all necessary conditions for a configuration
    in the ghost semantics to make progress (see [ghost_sos_progress] for the proof). *)

Inductive ghost_abort : Heap -> ProcMap -> Store -> Store -> GhostCmd -> Prop :=
  (* heap read *)
  | gabort_read h pm s g x E :
    h (expr_denot E s) = None ->
    ghost_abort h pm s g (Cread x E)
  (* heap write *)
  | gabort_write h pm s g E1 E2 :
    h (expr_denot E1 s) = None ->
    ghost_abort h pm s g (Cwrite E1 E2)
  (* heap allocation *)
  | gabort_alloc h pm s g x E :
    (~ exists l, h l = None) ->
    ghost_abort h pm s g (Calloc x E)
  (* heap dispose *)
  | gabort_dispose h pm s g E :
    h (expr_denot E s) = None ->
    ghost_abort h pm s g (Cdispose E)
  (* sequential composition *)
  | gabort_seq h pm s g C1 C2 :
    ghost_abort h pm s g C1 ->
    ghost_abort h pm s g (Cseq C1 C2)
  (* atomic programs *)
  | gabort_atom h pm s g C :
    ghost_abort h pm s g C ->
    ghost_abort h pm s g (Cinatom C)
  (* parallel - left *)
  | gabort_par_l h pm s g C1 C2 :
    ghost_abort h pm s g C1 ->
    ~ cmd_locked C2 ->
    ghost_abort h pm s g (Cpar C1 C2)
  (* parallel - right *)
  | gabort_par_r h pm s g C1 C2 :
    ghost_abort h pm s g C2 ->
    ~ cmd_locked C1 ->
    ghost_abort h pm s g (Cpar C1 C2)
  (* parallel - deadlock *)
  | gabort_par_deadlock h pm s g C1 C2 :
    cmd_locked C1 ->
    cmd_locked C2 ->
    ghost_abort h pm s g (Cpar C1 C2)
  (* action - step *)
  | gabort_act_step h pm s g m C :
    ghost_abort h pm s g C ->
    ghost_abort h pm s g (Cinact m C)
  (* action - end, case 1 *)
  | gabort_act_end_1 h pm s g pid a hs :
    (~ pmv_occ (pm pid)) ->
    ghost_abort h pm s g (Cinact (pid, a, hs) Cskip)
  (* action - end, case 2 *)
  | gabort_act_end_2 h pm s g pid a hs q p P xs f :
    pmv_eq (pm pid) (PMelem q p P xs f) ->
    (exists x, In x xs /\ hs (f x) = None) ->
    ghost_abort h pm s g (Cinact (pid, a, hs) Cskip)
  (* action - end, case 3 *)
  | gabort_act_end_3 h pm s g pid a hs q p P xs f :
    pmv_eq (pm pid) (PMelem q p P xs f) ->
    (exists x, In x xs /\ h (f x) = None) ->
    ghost_abort h pm s g (Cinact (pid, a, hs) Cskip)
  (* action - end, case 4 *)
  | gabort_act_end_4 h pm s g pid a hs q p P xs f ps1 ps2 :
    pmv_eq (pm pid) (PMelem q p P xs f) ->
      (forall x, In x xs -> hs (f x) = Some (ps1 x)) ->
      (forall x, In x xs -> h (f x) = Some (ps2 x)) ->
      (~ exists P', proc_sos P ps1 a P' ps2) ->
    ghost_abort h pm s g (Cinact (pid, a, hs) Cskip)
  (* process - init *)
  | gabort_proc_init h pm s g x p xs f :
    (~ exists pid, pm pid = PMfree) ->
    ghost_abort h pm s g (Cproc x p xs f)
  (* process - end, case 1 *)
  | gabort_proc_end_1 h pm s g x :
    ~ pmv_full (pm (g x)) ->
    ghost_abort h pm s g (Cendproc x)
  (* process - end, case 2 *)
  | gabort_proc_end_2 h pm s g x p P xs f :
    pmv_eq (pm (g x)) (PMelem perm_full p P xs f) ->
    ~ proc_term P ->
    ghost_abort h pm s g (Cendproc x)
  (* data race - case 1 *)
  | gabort_race_l h pm s g C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_writes C1 s) (cmd_acc C2 s) ->
    ghost_abort h pm s g (Cpar C1 C2)
  (* data race - case 2 *)
  | gabort_race_r h pm s g C1 C2 :
    ~ cmd_locked C1 ->
    ~ cmd_locked C2 ->
    ~ disjoint (cmd_acc C1 s) (cmd_writes C2 s) ->
    ghost_abort h pm s g (Cpar C1 C2).

Add Search Blacklist "ghost_abort_ind".

(** The program abort semantics is embedded in the ghost abort semantics. *)

Theorem prog_abort_emb :
  forall C h pm s g,
  prog_abort h s (plain C) ->
  ghost_abort h pm s g C.
Proof.
  induction C; intros h pm s g ABORT; simpls; inv ABORT; clear ABORT; vauto.
  (* sequential composition *)
  - constructor. by apply IHC1.
  (* parallel composition - left *)
  - apply gabort_par_l.
    + by apply IHC1.
    + by rewrite <- cmd_locked_plain.
  (* parallel composition - right *)
  - apply gabort_par_r.
    + by apply IHC2.
    + by rewrite <- cmd_locked_plain.
  (* parallel composition - deadlock *)
  - apply gabort_par_deadlock; by rewrite <- cmd_locked_plain.
  (* data race - case 1 *)
  - apply gabort_race_l.
    + intro H2. apply H1. by rewrite cmd_locked_plain.
    + intro H2. apply H4. by rewrite cmd_locked_plain.
    + intro H2. apply H5. rewrite cmd_writes_plain.
      by rewrite cmd_acc_plain.
  (* data race - case 2 *)
  - apply gabort_race_r.
    + intro H2. apply H1. by rewrite cmd_locked_plain.
    + intro H2. apply H4. by rewrite cmd_locked_plain.
    + intro H2. apply H5. rewrite cmd_writes_plain.
      by rewrite cmd_acc_plain.
  (* atomic programs *)
  - constructor. by apply IHC.
  (* action programs *)
  - constructor. by apply IHC.
Qed.

(** Progress of ghost program execution: every configuration that does not abort
    can either make a computation step in the ghost semantics, or has already terminated. *)

Lemma heap_procvar_cover :
  forall (xs : list ProcVar)(h : Heap)(f : ProcVar -> Loc),
    (forall x, In x xs -> h (f x) <> None) ->
  exists g : ProcVar -> Val,
    forall x, In x xs -> h (f x) = Some (g x).
Proof.
  induction xs; intros h f H1.
  (* base case *)
  - simpls. exists (fun _ => 0%Z).
    intros x H2. contradiction.
  (* induction case *)
  - specialize IHxs with h f.
    cut (forall x, In x xs -> h (f x) <> None).
    + intros H2. apply IHxs in H2.
      destruct H2 as (g & H2).
      cut (exists v, h (f a) = Some v).
      * intro H3. destruct H3 as (v & H3).
        exists (update g a v).
        intros y H4. unfold update. desf.
        simpls. desf. by apply H2.
      * rewrite <- option_not_none.
        apply H1. vauto.
    + intros x H2. apply H1. simpls. intuition.
Qed.

Theorem ghost_sos_progress :
  forall C h pm s g,
  ~ ghost_abort h pm s g C ->
  C = Cskip \/ exists C' h' pm' s' g', ghost_sos h pm s g C h' pm' s' g' C'.
Proof.
  induction C; intros h pm s g ABORT.
  (* empty programs *)
  - by left.
  (* sequential composition *)
  - cut (C1 = Cskip \/ ~ C1 = Cskip); [|apply classic].
    intros [H | H]; right.
    (* left program [C1] is empty *)
    + clarify. exists C2, h, pm, s, g. vauto.
    (* left program [C1] is not empty *)
    + assert (H1 : ~ ghost_abort h pm s g C1). {
      intro H1. apply ABORT. vauto. }
      apply IHC1 in H1.
      destruct H1 as [H1 | H1]; vauto.
      destruct H1 as (C1' & h' & pm' & s' & g' & STEP).
      exists (Cseq C1' C2), h', pm', s', g'. vauto.
  (* local assignment *)
  - right. exists Cskip, h, pm, (update s x (expr_denot E s)), g. vauto.
  (* heap reading *)
  - right. cut (exists v, h (expr_denot E s) = Some v).
    + intro H1. destruct H1 as (v & H1).
      exists Cskip, h, pm, (update s x v), g. vauto.
    + rewrite <- option_not_none.
      intro H1. apply ABORT. vauto.
  (* heap writing *)
  - right. cut (exists v, h (expr_denot E1 s) = Some v).
    + intro H1. destruct H1 as (v & H1).
      exists Cskip, (update h (expr_denot E1 s) (Some (expr_denot E2 s))), pm, s, g.
      by apply gsos_write with v.
    + rewrite <- option_not_none.
      intro H. apply ABORT. vauto.
  (* if-then-else *)
  - right. cut (bexpr_denot B s = true \/ bexpr_denot B s = false).
    + intro H1. destruct H1 as [H1 | H1].
      exists C1, h, pm, s, g. vauto.
      exists C2, h, pm, s, g. vauto.
    + rewrite <- Bool.not_true_iff_false.
      apply classic.
  (* while-loops *)
  - right. exists (Cite B (Cseq C (Cwhile B C)) Cskip), h, pm, s, g. vauto.
  (* parallel composition *)
  - right.
    cut ((~ cmd_locked C2 /\ exists C1' h' pm' s' g', ghost_sos h pm s g C1 h' pm' s' g' C1') \/
         (~ cmd_locked C1 /\ exists C2' h' pm' s' g', ghost_sos h pm s g C2 h' pm' s' g' C2') \/
          C1 = Cskip /\ C2 = Cskip).
    (* progress for all three cases in the cut *)
    + intro H. destruct H as [H | [H | H]].
      (* [C1] makes a step *)
      * destruct H as (H & C1' & h' & pm' & s' & g' & STEP).
        exists (Cpar C1' C2), h', pm', s', g'. vauto.
      (* [C2] makes a step *)
      * destruct H as (H & C2' & h' & pm' & s' & g' & STEP).
        exists (Cpar C1 C2'), h', pm', s', g'. vauto.
      (* [C1] and [C2] have both terminated *)
      * destruct H as (H1 & H2). clarify.
        exists Cskip, h, pm, s, g. vauto.
    (* one of the three cases in the cut must hold *)
    + cut (C1 = Cskip \/ ~ C1 = Cskip); [|apply classic].
      cut (C2 = Cskip \/ ~ C2 = Cskip); [|apply classic].
      intros H1 H2. desf.
      (* [C1] and [C2] have both terminated *)
      * by repeat right.
      (* [C1] has terminated, [C2] has not *)
      * right. left. split.
        intro H2. inv H2.
        apply imply_and_or with (C2 = Cskip); vauto.
        apply IHC2. intro ABORT'.
        apply ABORT. by constructor.
      (* [C2] has terminated, [C1] has not *)
      * left. split. intro H3. inv H3.
        apply imply_and_or with (C1 = Cskip); vauto.
        apply IHC1. intro ABORT'.
        apply ABORT. by constructor.
      (* [C1] and [C2] have both not terminated *)
      * cut (cmd_locked C1 \/ ~ cmd_locked C1); [|apply classic].
        intro H3. destruct H3 as [H3 | H3].
        (* [C1] is locked *)
        ** assert (H4 : ~ cmd_locked C2). {
           intro H4. apply ABORT. by constructor. }
           left. split. auto.
           apply imply_and_or with (C1 = Cskip); vauto.
           apply IHC1. intro ABORT'.
           apply ABORT. by constructor.
        (* [C1] is not locked *)
        ** right. left. split. auto.
           apply imply_and_or with (C2 = Cskip); vauto.
           apply IHC2. intro ABORT'.
           apply ABORT. by constructor.
  (* heap allocation *)
  - right. cut (exists l, h l = None).
    + intro H. destruct H as (l & H).
      exists Cskip, (update h l (Some (expr_denot E s))), pm, (update s x l), g.
      by constructor.
    + apply NNPP. intro H.
      apply ABORT. by constructor.
  (* heap disposal *)
  - right.
    exists Cskip, (update h (expr_denot E s) None), pm, s, g.
    constructor.
  (* atomic block - init *)
  - right. exists (Cinatom C), h, pm, s, g. constructor.
  (* atomic block - step *)
  - right. cut (C = Cskip \/ ~ C = Cskip); [|apply classic].
    intro H. destruct H as [H | H].
    (* [C] has terminated *)
    + clarify. exists Cskip, h, pm, s, g. vauto.
    (* [C] has not terminated *)
    + cut (~ ghost_abort h pm s g C).
      * intro H1. apply IHC in H1.
        destruct H1 as [H1 | H1]; vauto.
        destruct H1 as (C' & h' & pm' & s' & g' & STEP).
        exists (Cinatom C'), h', pm', s', g'. vauto.
      * intro H1. apply ABORT. vauto.
  (* process - init *)
  - right. cut (exists pid, pm pid = PMfree).
    + intro H. destruct H as (pid & H).
      pose (P := body p).
      pose (f' := expr_denot_map f s).
      pose (pmv := PMelem perm_full p P xs f').
      exists Cskip, h, (update pm pid pmv), s, (update g x pid).
      by constructor.
    + apply NNPP. intro H.
      apply ABORT. by constructor.
  (* action - init *)
  - right. exists (Cinact (g x, a, h) C), h, pm, s, g. vauto.
  (* action - step *)
  - right. cut (C = Cskip \/ ~ C = Cskip); [|apply classic].
    intro H. destruct H as [H | H].
    (* [C] has terminated *)
    + clarify.
      destruct m as ((pid, a) & hs).
      assert (K1 : pmv_occ (pm pid)). {
        apply NNPP. intro K1. apply ABORT. vauto. }
      apply pmv_occ_destruct in K1.
      destruct K1 as (q & p & P & xs & F & K1).
      assert (K2 : exists ps1, forall x : ProcVar, In x xs -> hs (F x) = Some (ps1 x)). {
        apply heap_procvar_cover.
        intros x K2 K3. apply ABORT.
        apply gabort_act_end_2 with (q := q)(p := p)(P := P)(xs := xs)(f := F); vauto.
        by rewrite K1. }
      assert (K3 : exists ps2, forall x : ProcVar, In x xs -> h (F x) = Some (ps2 x)). {
        apply heap_procvar_cover.
        intros x K3 K4. apply ABORT.
        apply gabort_act_end_3 with (q := q)(p := p)(P := P)(xs := xs)(f := F); vauto.
        by rewrite K1. }
      destruct K2 as (ps1 & K2).
      destruct K3 as (ps2 & K3).
      assert (K4 : exists P', proc_sos P ps1 a P' ps2). {
        apply NNPP. intro K4. apply ABORT.
        apply gabort_act_end_4 with q p P xs F ps1 ps2; vauto.
        by rewrite K1. }
      destruct K4 as (P' & K4).
      pose (pm' := update pm pid (PMelem q p P' xs F)).
      exists Cskip, h, pm', s, g.
      apply gsos_act_skip with P ps1 ps2; vauto.
      by rewrite K1.
    (* [C] has not terminated *)
    + cut (~ ghost_abort h pm s g C).
      * intro H1. apply IHC in H1.
        destruct H1 as [H1 | H1]; vauto.
        destruct H1 as (C' & h' & pm' & s' & g' & STEP).
        exists (Cinact m C'), h', pm', s', g'. vauto.
      * intro H1. apply ABORT. vauto.
  (* process - end *)
  - right. pose (pid := g x).
    exists Cskip, h, (update pm pid PMfree), s, g.
    assert (H1 : pmv_full (pm pid)). {
      apply NNPP. intro H. apply ABORT. vauto. }
    apply pmv_full_content in H1.
    destruct H1 as (p & P & xs & f & H1).
    assert (H2 : proc_term P). {
      apply NNPP. intro H. apply ABORT. subst pid.
      apply gabort_proc_end_2 with p P xs f; vauto.
      rewrite H1. auto. }
    apply gsos_proc_end with p P xs f; vauto.
    subst pid. by rewrite H1.
Qed.

(** The aborting of ghost programs is stable under replacement of process maps with bisimilar ones,
    as well as replacement of (ghost) stores with stores that agree on all variables occuring
    free in the program. *)

Lemma ghost_abort_procmap_eq :
  forall C h pm1 pm2 s g,
  procmap_eq pm1 pm2 ->
  ghost_abort h pm1 s g C ->
  ghost_abort h pm2 s g C.
Proof.
  induction C; intros h pm1 pm2 s g EQ ABORT; simpls;
    inv ABORT; clear ABORT; vauto.
  (* sequential composition *)
  - constructor. by apply IHC1 with pm1.
  (* parallel composition - left *)
  - apply gabort_par_l. by apply IHC1 with pm1.
    intro H1. by apply H6.
  (* parallel composition - left *)
  - apply gabort_par_r. by apply IHC2 with pm1.
    intro H1. by apply H6.
  (* atomic programs *)
  - constructor. by apply IHC with pm1.
  (* process - init *)
  - constructor. intro H.
    apply H4. destruct H as (pid & H).
    exists pid. apply procmap_eq_free with pm2; auto.
  (* action - step *)
  - constructor. by apply IHC with pm1.
  (* action - end, case 1 *)
  - apply gabort_act_end_1. intro H1.
    red in EQ. specialize EQ with pid.
    rewrite <- EQ in H1. congruence.
  (* action - end, case 2 *)
  - destruct H6 as (x & H1 & H2).
    unfold procmap_eq in EQ.
    specialize EQ with pid.
    rewrite H5 in EQ.
    unfold pmv_eq in EQ.
    remember (pm2 pid) as pm2v.
    destruct pm2v as [q' p' P' xs' f'| |]; vauto.
    desf. apply gabort_act_end_2 with q' p' P' xs' f'; vauto.
    + by rewrite Heqpm2v.
    + exists x. split; vauto.
      apply map_eq_In with (x0 := x) in EQ3; vauto.
      by rewrite <- EQ3.
  (* action - end, case 3 *)
  - destruct H6 as (x & H1 & H2).
    unfold procmap_eq in EQ.
    specialize EQ with pid.
    rewrite H5 in EQ.
    unfold pmv_eq in EQ.
    remember (pm2 pid) as pm2v.
    destruct pm2v as [q' p' P' xs' f' | _ | _]; vauto.
    desf. apply gabort_act_end_3 with q' p' P' xs' f'; vauto.
    + by rewrite Heqpm2v.
    + exists x. split; vauto.
      apply map_eq_In with (x0 := x) in EQ3; vauto.
      by rewrite <- EQ3.
  (* action - end, case 4 *)
  - unfold procmap_eq in EQ.
    specialize EQ with pid.
    rewrite H1 in EQ.
    unfold pmv_eq in EQ.
    remember (pm2 pid) as pm2v.
    destruct pm2v as [q' p' P' xs' f' | _ | _]; vauto. desf.
    apply gabort_act_end_4 with q' p' P' xs' f' ps1 ps2; vauto.
    + by rewrite Heqpm2v.
    + intros x H3.
      apply map_eq_In with (x0 := x) in EQ3; vauto.
      rewrite <- EQ3. by apply H2.
    + intros x H3.
      apply map_eq_In with (x0 := x) in EQ3; vauto.
      rewrite <- EQ3. by apply H7.
    + intros H3. destruct H3 as (P'' & H3).
      inv EQ1. destruct H as (D1 & D2 & D3 & D4).
      apply D2 in H3. destruct H3 as (Q & H3 & H4).
      apply H8. exists Q. done.
  (* process - end, case 1 *)
  - apply gabort_proc_end_1.
    unfold procmap_eq in EQ. specialize EQ with (g x).
    by rewrite <- EQ.
  (* process - end, case 2 *)
  - generalize EQ. intro EQ'.
    unfold procmap_eq in EQ.
    specialize EQ with (g x).
    rewrite H0 in EQ.
    unfold pmv_eq in EQ.
    remember (pm2 (g x)) as pm2v.
    destruct pm2v as [q' p' P' xs' f' | _ | _]; vauto.
    desf. apply gabort_proc_end_2 with p' P' xs' f'; auto.
    + unfold procmap_eq in EQ'.
      specialize EQ' with (g x).
      rewrite <- EQ', H0. vauto.
    + intro H. apply H5.
      inv EQ1. destruct H1 as (D1 & D2 & D3 & D4).
      by apply D4.
Qed.

Add Parametric Morphism : ghost_abort
  with signature eq ==> procmap_eq ==> eq ==> eq ==> eq ==> iff
    as ghost_abort_procmap_mor.
Proof.
  intros h pm1 pm2 H1 s g C. split; intro H2.
  by apply ghost_abort_procmap_eq with pm1.
  apply ghost_abort_procmap_eq with pm2; auto.
Qed.

Lemma ghost_abort_agree :
  forall C h pm s1 s2 g,
    (forall x, cmd_fv C x -> s1 x = s2 x) ->
  ghost_abort h pm s1 g C ->
  ghost_abort h pm s2 g C.
Proof.
  induction C; intros h pm s1 s2 g AGR ABORT; simpls;
    inv ABORT; clear ABORT; vauto.
  (* sequential composition *)
  - constructor. apply IHC1 with s1; vauto.
    intros x H1. apply AGR. by left.
  (* heap reading *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
    unfold store_agree. intros y H.
    apply AGR. by right.
  (* heap writing *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
    unfold store_agree. intros x H.
    apply AGR. by left.
  (* parallel - left *)
  - apply gabort_par_l; vauto.
    apply IHC1 with s1; auto.
  (* parallel - right *)
  - apply gabort_par_r; vauto.
    apply IHC2 with s1; auto.
  (* data race, case 1 *)
  - apply gabort_race_l; auto.
    intro H2. apply H7.
    red. intros l F1 F2.
    rewrite cmd_writes_agree with (s4 := s2) in F1; auto.
    rewrite cmd_acc_agree with (s4 := s2) in F2; auto.
    by apply H2 with l.
  (* data race, case 2 *)
  - apply gabort_race_r; auto.
    intro H2. apply H7.
    red. intros l F1 F2.
    rewrite cmd_acc_agree with (s4 := s2) in F1; auto.
    rewrite cmd_writes_agree with (s4 := s2) in F2; auto.
    by apply H2 with l.
  (* heap disposal *)
  - constructor.
    rewrite <- expr_agree with (s1 := s1); auto.
  (* atomic programs *)
  - constructor. apply IHC with s1; auto.
  (* action block *)
  - constructor. apply IHC with s1; auto.
Qed.

Lemma ghost_abort_agree_g :
  forall C h pm s g1 g2,
    (forall x, cmd_fv C x -> g1 x = g2 x) ->
  ghost_abort h pm s g1 C ->
  ghost_abort h pm s g2 C.
Proof.
  induction C; intros h pm s g1 g2 AGR ABORT; simpls;
    inv ABORT; clear ABORT; vauto.
  (* sequential composition *)
  - constructor. apply IHC1 with g1; auto.
  (* parallel - left *)
  - apply gabort_par_l; auto.
    apply IHC1 with g1; auto.
  (* parallel - right *)
  - apply gabort_par_r; vauto.
    apply IHC2 with g1; auto.
  (* atomic programs *)
  - constructor. apply IHC with g1; auto.
  (* action - step *)
  - constructor. apply IHC with g1; auto.
  (* process - end, case 1 *)
  - apply gabort_proc_end_1.
    rewrite <- AGR; vauto.
  (* process - end, case 2 *)
  - apply gabort_proc_end_2 with p P xs f; vauto.
    rewrite <- AGR; vauto.
Qed.
