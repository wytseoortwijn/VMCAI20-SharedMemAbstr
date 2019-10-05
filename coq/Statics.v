Require Import Bool.
Require Import HahnBase.
Require Import List.
Require Import Prerequisites.
Require Import Process.
Require Import Setoid.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.

Set Implicit Arguments.


(** * Statics *)

(** This section defines the syntactic structure of programs,
    as well as program well-formedness, free- and modified variables, and substitution. *)

Definition Var := Z.


(** ** Syntax *)

(** Commands are parameterised by a type, which is the type of the
    metadata that is stored in action blocks (see the [Cinact] constructor for this).
    We later define a ghost operational semantics (in Dynamics.v) in which the metadata
    component is used to maintain and convey extra runtime information regarding abstract models. *)

Inductive Expr :=
  | Econst(n:Z)
  | Evar(x:Var)
  | Eplus(E1 E2:Expr).

Add Search Blacklist "Expr_rect".
Add Search Blacklist "Expr_ind".
Add Search Blacklist "Expr_rec".

Inductive BoolExpr :=
  | Bconst(b:bool)
  | Bnot(B:BoolExpr)
  | Band(B1 B2:BoolExpr)
  | Beq(E1 E2:Expr).

Add Search Blacklist "BoolExpr_rect".
Add Search Blacklist "BoolExpr_ind".
Add Search Blacklist "BoolExpr_rec".

Inductive Cmd (T : Type) :=
  | Cskip
  | Cseq(C1 C2:Cmd T)
  | Cass(x:Var)(E:Expr)
  | Cread(x:Var)(E:Expr)
  | Cwrite(E1 E2:Expr)
  | Cite(B:BoolExpr)(C1 C2:Cmd T)
  | Cwhile(B:BoolExpr)(C:Cmd T)
  | Cpar(C1 C2:Cmd T)
  | Calloc(x:Var)(E:Expr)
  | Cdispose(E:Expr)
  | Catomic(C:Cmd T)
  | Cinatom(C:Cmd T)
  | Cproc(x:Var)(p:ProcLabel)(xs:list ProcVar)(f:ProcVar -> Expr)
  | Cact(x:Var)(a:ActLabel)(C:Cmd T)
  | Cinact(m:T)(C:Cmd T)
  | Cendproc(x:Var).

Add Search Blacklist "Cmd_rect".
Add Search Blacklist "Cmd_ind".
Add Search Blacklist "Cmd_rec".

Arguments Cskip {_}.
Arguments Cseq {_}.
Arguments Cass {_}.
Arguments Cread {_}.
Arguments Cwrite {_}.
Arguments Cite {_}.
Arguments Cwhile {_}.
Arguments Cpar {_}.
Arguments Calloc {_}.
Arguments Cdispose {_}.
Arguments Catomic {_}.
Arguments Cinatom {_}.
Arguments Cproc {_}.
Arguments Cact {_}.
Arguments Cinact {_}.
Arguments Cendproc {_}.

Lemma cmd_neg_seq {T} :
  forall C2 C1 : Cmd T,
  ~ C2 = Cseq C1 C2.
Proof.
  induction C2; ins. intro. vauto.
  by apply IHC2_2 in H.
Qed.

Lemma cmd_neg_ite_t {T} :
  forall (C1 C2 : Cmd T) B,
  ~ C1 = Cite B C1 C2.
Proof.
  induction C1; ins. intro. vauto.
  by apply IHC1_1 in H1.
Qed.

Lemma cmd_neg_ite_f {T} :
  forall (C2 C1 : Cmd T) B,
  ~ C2 = Cite B C1 C2.
Proof.
  induction C2; ins. intro. vauto.
  by apply IHC2_2 in H.
Qed.

Lemma expr_eq_dec :
  forall E1 E2 : Expr, { E1 = E2 } + { E1 <> E2 }.
Proof.
  decide equality; apply Z.eq_dec.
Qed.

Lemma bexpr_eq_dec :
  forall B1 B2 : BoolExpr, { B1 = B2 } + { B1 <> B2 }.
Proof.
  decide equality.
  apply bool_dec.
  apply expr_eq_dec.
  apply expr_eq_dec.
Qed.

(** Operations for converting process algebraic expressions to program expressions. *)

Fixpoint pexpr_convert (e : ProcExpr)(f : ProcVar -> Expr) : Expr :=
  match e with
    | PEconst n => Econst n
    | PEvar x => f x
    | PEplus e1 e2 => Eplus (pexpr_convert e1 f) (pexpr_convert e2 f)
  end.

Fixpoint pbexpr_convert (b : ProcBoolExpr)(f : ProcVar -> Expr) : BoolExpr :=
  match b with
    | PBconst b' => Bconst b'
    | PBnot b' => Bnot (pbexpr_convert b' f)
    | PBand b1 b2 => Band (pbexpr_convert b1 f) (pbexpr_convert b2 f)
    | PBeq e1 e2 => Beq (pexpr_convert e1 f) (pexpr_convert e2 f)
  end.


(** ** Plain commands *)

(** Plain commands are commands without metadata components (or, technically, these are commands
    in which the metadata type is fixed and chosen to have only one inhabitant, namely [PMnone]). *)

Inductive PlainMetadata := PMnone.

Add Search Blacklist "PlainMetadata_rec".
Add Search Blacklist "PlainMetadata_ind".
Add Search Blacklist "PlainMetadata_rect".

Definition PlainCmd : Type := Cmd PlainMetadata.

Fixpoint plain {T} (C : Cmd T) : PlainCmd :=
  match C with
    | Cskip => Cskip
    | Cseq C1 C2 => Cseq (plain C1) (plain C2)
    | Cass x E => Cass x E
    | Cread x E => Cread x E
    | Cwrite E1 E2 => Cwrite E1 E2
    | Cite B C1 C2 => Cite B (plain C1) (plain C2)
    | Cwhile B C' => Cwhile B (plain C')
    | Cpar C1 C2 => Cpar (plain C1) (plain C2)
    | Calloc x E => Calloc x E
    | Cdispose E => Cdispose E
    | Catomic C' => Catomic (plain C')
    | Cinatom C' => Cinatom (plain C')
    | Cproc x p xs f => Cproc x p xs f
    | Cact x a C' => Cact x a (plain C')
    | Cinact _ C' => Cinact PMnone (plain C')
    | Cendproc x => Cendproc x
  end.

Lemma plain_skip {T} :
  forall C : Cmd T,
  plain C = Cskip -> C = Cskip.
Proof.
  induction C; intro H; intuition vauto.
Qed.


(** ** User programs *)

(** A program is a _user program_ if it does not contain [Cinact] or [Cinatom] as a subprogram. *)

(** The program [Cinatom C] represents an atomic program [C] that is partially executed; such programs
    can not be written down by a user but are an artifact of the program dynamics. The same holds for
    [Cinact m C], which describes a partially executed action program [C] (and is a specification-only command besides). *)

Fixpoint cmd_user {T} (C : Cmd T) : Prop :=
  match C with
    | Cskip => True
    | Cseq C1 C2 => cmd_user C1 /\ cmd_user C2
    | Cass _ _ => True
    | Cread _ _ => True
    | Cwrite _ _ => True
    | Cite _ C1 C2 => cmd_user C1 /\ cmd_user C2
    | Cwhile _ C' => cmd_user C'
    | Cpar C1 C2 => cmd_user C1 /\ cmd_user C2
    | Calloc _ _ => True
    | Cdispose _ => True
    | Catomic C' => cmd_user C'
    | Cinatom _ => False
    | Cproc _ _ _ _ => True
    | Cact _ _ C' => cmd_user C'
    | Cinact _ _ => False
    | Cendproc _ => True
  end.

Lemma cmd_user_plain {T} :
  forall C : Cmd T,
  cmd_user C = cmd_user (plain C).
Proof.
  induction C; simpls; try (by rewrite IHC1, IHC2); by rewrite IHC.
Qed.


(** ** Locked programs *)

(** A program is defined to be _locked_ if it contains [Cinatom] as a subprogram. *)

Fixpoint cmd_locked {T} (C : Cmd T) : Prop :=
  match C with
    | Cseq C1 _ => cmd_locked C1
    | Cpar C1 C2 => cmd_locked C1 \/ cmd_locked C2
    | Cinact _ C1 => cmd_locked C1
    | Cinatom _ => True
    | _ => False
  end.

Lemma cmd_locked_plain {T} :
  forall C : Cmd T,
  cmd_locked (plain C) = cmd_locked C.
Proof.
  induction C; ins. by rewrite IHC1, IHC2.
Qed.


(** ** Well-formed programs *)

(** A program is defined to be _basic_ if it does not contain any process-related commands, and
    if there are no deadlocks in any of its parallel subprograms. *)

(** A program is _well-formed_ if [C] is basic for every subcommand [Cact _ _ C] that occurs in
    the program, and if there are no deadlocks in any of its parallel subprograms, likewise to basic programs. *)

Fixpoint cmd_basic {T} (C : Cmd T) : Prop :=
  match C with
    | Cskip => True
    | Cseq C1 C2 => cmd_basic C1 /\ cmd_basic C2
    | Cass _ _ => True
    | Cread _ _ => True
    | Cwrite _ _ => True
    | Cite _ C1 C2 => cmd_basic C1 /\ cmd_basic C2
    | Cwhile _ C' => cmd_basic C'
    | Cpar C1 C2 => cmd_basic C1 /\ cmd_basic C2 /\ ~ (cmd_locked C1 /\ cmd_locked C2)
    | Calloc _ _ => True
    | Cdispose _ => True
    | Catomic C' => cmd_basic C'
    | Cinatom C' => cmd_basic C'
    | Cproc _ _ _ _ => False
    | Cact _ _ _ => False
    | Cinact _ _ => False
    | Cendproc _ => False
  end.

Fixpoint cmd_wf {T} (C : Cmd T) : Prop :=
  match C with
    | Cskip => True
    | Cseq C1 C2 => cmd_wf C1 /\ cmd_wf C2
    | Cass _ _ => True
    | Cread _ _ => True
    | Cwrite _ _ => True
    | Cite _ C1 C2 => cmd_wf C1 /\ cmd_wf C2
    | Cwhile _ C' => cmd_wf C'
    | Cpar C1 C2 => cmd_wf C1 /\ cmd_wf C2 /\ ~ (cmd_locked C1 /\ cmd_locked C2)
    | Calloc _ _ => True
    | Cdispose _ => True
    | Catomic C' => cmd_wf C'
    | Cinatom C' => cmd_wf C'
    | Cproc _ _ _ _ => True
    | Cact _ _ C' => cmd_basic C'
    | Cinact _ C' => cmd_basic C'
    | Cendproc _ => True
  end.

Lemma cmd_basic_wf {T} :
  forall C : Cmd T, cmd_basic C -> cmd_wf C.
Proof.
  induction C; intro H; simpls; intuition vauto.
Qed.


(** ** Free variables *)

(** Free variables of (Boolean) expressions and programs are defined in the standard way. *)

Fixpoint expr_fv (E : Expr) : list Var :=
   match E with
    | Econst n => nil
    | Evar x => [x]
    | Eplus E1 E2 => expr_fv E1 ++ expr_fv E2
  end.

Fixpoint expr_list_fv (xs : list Expr) : list Var :=
  match xs with
    | nil => nil
    | E :: xs' => expr_fv E ++ expr_list_fv xs'
  end.

Definition expr_map_fv {T} (f : T -> Expr)(x : Var) : Prop :=
  exists t : T, In x (expr_fv (f t)).

Fixpoint bexpr_fv (B : BoolExpr) : list Var :=
   match B with
    | Bconst b => nil
    | Bnot B' => bexpr_fv B'
    | Band B1 B2 => bexpr_fv B1 ++ bexpr_fv B2
    | Beq E1 E2 => expr_fv E1 ++ expr_fv E2
  end.

Fixpoint cmd_fv {T} (C : Cmd T)(x : Var) : Prop :=
  match C with
    | Cskip => False
    | Cass y E
    | Cread y E
    | Calloc y E => x = y \/ In x (expr_fv E)
    | Cwrite E1 E2 => In x (expr_fv E1) \/ In x (expr_fv E2)
    | Cite B C1 C2 => In x (bexpr_fv B) \/ cmd_fv C1 x \/ cmd_fv C2 x
    | Cwhile B C' => In x (bexpr_fv B) \/ cmd_fv C' x
    | Cseq C1 C2
    | Cpar C1 C2 => cmd_fv C1 x \/ cmd_fv C2 x
    | Cdispose E => In x (expr_fv E)
    | Catomic C'
    | Cinatom C' => cmd_fv C' x
    | Cproc y _ xs f => x = y \/ expr_map_fv f x
    | Cact y _ C' => x = y \/ cmd_fv C' x
    | Cinact _ C' => cmd_fv C' x
    | Cendproc y => x = y
  end.

Lemma cmd_fv_plain {T} :
  forall C : Cmd T,
  cmd_fv C = cmd_fv (plain C).
Proof.
  induction C; simpls; try (by rewrite IHC1, IHC2); by rewrite IHC.
Qed.


(** ** Modified variables *)

(** The operation [cmd_mod] describes the set of variables that are _modified_ (written to) by
    a given program, and is defined in the standard way (however, note that, for later convenience,
    [cmd_mod] is defined as a predicate, rather than a fixpoint operation that yields a list of variables). *)

Fixpoint cmd_mod {T} (C : Cmd T)(x : Var) : Prop :=
  match C with
    | Cskip => False
    | Cass y _
    | Cread y _ => x = y
    | Cwrite _ _ => False
    | Cseq C1 C2
    | Cpar C1 C2
    | Cite _ C1 C2 => cmd_mod C1 x \/ cmd_mod C2 x
    | Cwhile _ C' => cmd_mod C' x
    | Calloc y _ => x = y
    | Cdispose _ => False
    | Catomic C' => cmd_mod C' x
    | Cinatom C' => cmd_mod C' x
    | Cproc y _ _ _ => x = y
    | Cact _ _ C'
    | Cinact _ C' => cmd_mod C' x
    | Cendproc _ => False
  end.

Lemma cmd_fv_mod {T} :
  forall (C : Cmd T)(x : Var),
  cmd_mod C x -> cmd_fv C x.
Proof.
  induction C; intros y H; simpls; vauto.
  - destruct H as [H | H].
    left. by apply IHC1.
    right. by apply IHC2.
  - destruct H as [H | H].
    right. left. by apply IHC1.
    right. right. by apply IHC2.
  - right. by apply IHC.
  - destruct H as [H | H].
    left. by apply IHC1.
    right. by apply IHC2.
  - by apply IHC.
  - by apply IHC.
  - right. by apply IHC.
  - by apply IHC.
Qed.

Lemma cmd_mod_plain {T} :
  forall C : Cmd T,
  cmd_mod C = cmd_mod (plain C).
Proof.
  induction C; simpls; by rewrite IHC1, IHC2.
Qed.


(** ** Substitution *)

(** Substitution in (Boolean) expressions is defined in the standard way. Moreover, the definition [expr_subst_map]
    lifts substitution in arithmetic expressions to substitutions in functions ranging over expressions. *)

Fixpoint expr_subst (x : Var)(E E' : Expr) : Expr :=
  match E' with
    | Econst n => Econst n
    | Evar y => if Z.eq_dec x y then E else Evar y
    | Eplus E1 E2 => Eplus (expr_subst x E E1) (expr_subst x E E2)
  end.

Definition expr_subst_map {T} (x : Var)(E : Expr)(f : T -> Expr) : T -> Expr :=
  fun y : T => expr_subst x E (f y).

Fixpoint bexpr_subst (x : Var)(E : Expr)(B : BoolExpr) : BoolExpr :=
  match B with
    | Bconst b => Bconst b
    | Bnot B' => Bnot (bexpr_subst x E B')
    | Band B1 B2 => Band (bexpr_subst x E B1) (bexpr_subst x E B2)
    | Beq E1 E2 => Beq (expr_subst x E E1) (expr_subst x E E2)
  end.

(** Standard (syntactic) properties of substitution. *)

Lemma expr_subst_pres :
  forall E1 E2 x,
  ~ In x (expr_fv E1) -> expr_subst x E2 E1 = E1.
Proof.
  induction E1; intros E2 x' H; simpls; intuition desf.
  rewrite IHE1_1, IHE1_2; auto.
  - intro H1. apply H.
    apply in_or_app. by right.
  - intro H1. apply H.
    apply in_or_app. by left.
Qed.

Lemma bexpr_subst_pres :
  forall B E x,
  ~ In x (bexpr_fv B) -> bexpr_subst x E B = B.
Proof.
  induction B; intros E x H; simpls.
  - by rewrite IHB.
  - rewrite IHB1, IHB2; intuition.
  - repeat rewrite expr_subst_pres; intuition.
Qed.

Lemma expr_subst_pres_map {T} :
  forall (f : T -> Expr) E x,
  ~ expr_map_fv f x -> expr_subst_map x E f = f.
Proof.
  intros f E x H1.
  extensionality t. apply expr_subst_pres.
  intro H2. apply H1. by exists t.
Qed.
