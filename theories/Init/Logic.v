(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Set Implicit Arguments.

Set Universe Polymorphism.

Require Export Notations.
Require Import Ltac.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

(** * SPropositional connectives *)

(** [True] is the always true SProposition *)

Inductive True : SProp :=
  I : True.

Register True as core.True.type.
Register I as core.True.I.

(** [False] is the always false SProposition *)
Inductive False : SProp :=.

Register False as core.False.type.

Inductive SFalse : SProp :=.

Register SFalse as core.False.type.


(** [not A], written [~A], is the negation of [A] *)

Definition not (A:SProp) := A -> SFalse.

Notation "'~' x" := (not x) : type_scope.

Register not as core.not.type.

(** Negation of a type in [Type] *)

Definition notT (A:Type) := A -> False.

(** Create the "core" hint database, and set its transparent state for
  variables and constants explicitly. *)

Create HintDb core.
#[global]
Hint Variables Opaque : core.
#[global]
Hint Constants Opaque : core.

#[global]
Hint Unfold not: core.

  (** [and A B], written [A /\ B], is the conjunction of [A] and [B]

      [conj p q] is a proof of [A /\ B] as soon as
      [p] is a proof of [A] and [q] a proof of [B]

      [proj1] and [proj2] are first and second projections of a conjunction *)

Inductive and (A B: SProp) : SProp :=
  conj : A -> B -> A /\ B

where "A /\ B" := (and A B) : type_scope.

Register and as core.and.type.
Register conj as core.and.conj.

Section Conjunction.

  Variables A B : SProp.

  Theorem proj1 : A /\ B -> A.
  Proof.
    destruct 1; trivial.
  Qed.

  Theorem proj2 : A /\ B -> B.
  Proof.
    destruct 1; trivial.
  Qed.

End Conjunction.

(** [or A B], written [A \/ B], is the disjunction of [A] and [B] *)

Inductive or (A B:SProp) : SProp :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B

where "A \/ B" := (or A B) : type_scope.

Arguments or_introl [A B] _, [A] B _.
Arguments or_intror [A B] _, A [B] _.

Register or as core.or.type.

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B:SProp) := (A -> B) /\ (B -> A) : SProp.

Notation "A <-> B" := (iff A B) : type_scope.

Register iff as core.iff.type.
Register proj1 as core.iff.proj1.
Register proj2 as core.iff.proj2.

Section Equivalence.

Theorem iff_refl : forall A:SProp, A <-> A.
  Proof.
    split; auto.
  Qed.

Theorem iff_trans : forall A B C:SProp, (A <-> B) -> (B <-> C) -> (A <-> C).
  Proof.
    intros A B C [H1 H2] [H3 H4]; split; auto.
  Qed.

Theorem iff_sym : forall A B:SProp, (A <-> B) -> (B <-> A).
  Proof.
    intros A B [H1 H2]; split; auto.
  Qed.

End Equivalence.

#[global]
Hint Unfold iff: extcore.

(** Backward direction of the equivalences above does not need assumptions *)

Theorem and_iff_compat_l : forall A B C : SProp,
  (B <-> C) -> (A /\ B <-> A /\ C).
Proof.
  intros ? ? ? [Hl Hr]; split; intros [? ?]; (split; [ assumption | ]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem and_iff_compat_r : forall A B C : SProp,
  (B <-> C) -> (B /\ A <-> C /\ A).
Proof.
  intros ? ? ? [Hl Hr]; split; intros [? ?]; (split; [ | assumption ]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem or_iff_compat_l : forall A B C : SProp,
  (B <-> C) -> (A \/ B <-> A \/ C).
Proof.
  intros ? ? ? [Hl Hr]; split; (intros [?|?]; [left; assumption| right]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem or_iff_compat_r : forall A B C : SProp,
  (B <-> C) -> (B \/ A <-> C \/ A).
Proof.
  intros ? ? ? [Hl Hr]; split; (intros [?|?]; [left| right; assumption]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem imp_iff_compat_l : forall A B C : SProp,
  (B <-> C) -> ((A -> B) <-> (A -> C)).
Proof.
  intros ? ? ? [Hl Hr]; split; intros H ?; [apply Hl | apply Hr]; apply H; assumption.
Qed.

Theorem imp_iff_compat_r : forall A B C : SProp,
  (B <-> C) -> ((B -> A) <-> (C -> A)).
Proof.
  intros ? ? ? [Hl Hr]; split; intros H ?; [apply H, Hr | apply H, Hl]; assumption.
Qed.

Theorem not_iff_compat : forall A B : SProp,
  (A <-> B) -> (~ A <-> ~B).
Proof.
  intros; apply imp_iff_compat_r; assumption.
Qed.


(** Some equivalences *)

Theorem neg_false : forall A : SProp, ~ A <-> (A <-> SFalse).
Proof.
  intro A; unfold not; split.
  - intro H; split; [exact H | intro H1; elim H1].
  - intros [H _]; exact H.
Qed.

Theorem and_cancel_l : forall A B C : SProp,
  (B -> A) -> (C -> A) -> ((A /\ B <-> A /\ C) <-> (B <-> C)).
Proof.
  intros A B C Hl Hr.
  split; [ | apply and_iff_compat_l]; intros [HypL HypR]; split; intros.
  + apply HypL; split; [apply Hl | ]; assumption.
  + apply HypR; split; [apply Hr | ]; assumption.
Qed.

Theorem and_cancel_r : forall A B C : SProp,
  (B -> A) -> (C -> A) -> ((B /\ A <-> C /\ A) <-> (B <-> C)).
Proof.
  intros A B C Hl Hr.
  split; [ | apply and_iff_compat_r]; intros [HypL HypR]; split; intros.
  + apply HypL; split; [ | apply Hl ]; assumption.
  + apply HypR; split; [ | apply Hr ]; assumption.
Qed.

Theorem and_comm : forall A B : SProp, A /\ B <-> B /\ A.
Proof.
  intros; split; intros [? ?]; split; assumption.
Qed.

Theorem and_assoc : forall A B C : SProp, (A /\ B) /\ C <-> A /\ B /\ C.
Proof.
  intros; split; [ intros [[? ?] ?]| intros [? [? ?]]]; repeat split; assumption.
Qed.

Theorem or_cancel_l : forall A B C : SProp,
  (B -> ~ A) -> (C -> ~ A) -> ((A \/ B <-> A \/ C) <-> (B <-> C)).
Proof.
  intros ? ? ? Fl Fr; split; [ | apply or_iff_compat_l]; intros [Hl Hr]; split; intros.
  { destruct Hl; [ right | destruct Fl | ]; assumption. }
  { destruct Hr; [ right | destruct Fr | ]; assumption. }
Qed.

Theorem or_cancel_r : forall A B C : SProp,
  (B -> ~ A) -> (C -> ~ A) -> ((B \/ A <-> C \/ A) <-> (B <-> C)).
Proof.
  intros ? ? ? Fl Fr; split; [ | apply or_iff_compat_r]; intros [Hl Hr]; split; intros.
  { destruct Hl; [ left | | destruct Fl ]; assumption. }
  { destruct Hr; [ left | | destruct Fr ]; assumption. }
Qed.

Theorem or_comm : forall A B : SProp, (A \/ B) <-> (B \/ A).
Proof.
  intros; split; (intros [? | ?]; [ right | left ]; assumption).
Qed.

Theorem or_assoc : forall A B C : SProp, (A \/ B) \/ C <-> A \/ B \/ C.
Proof.
  intros; split; [ intros [[?|?]|?]| intros [?|[?|?]]].
  + left; assumption.
  + right; left; assumption.
  + right; right; assumption.
  + left; left; assumption.
  + left; right; assumption.
  + right; assumption.
Qed.
Lemma iff_and : forall A B : SProp, (A <-> B) -> (A -> B) /\ (B -> A).
Proof.
  intros A B []; split; trivial.
Qed.

Lemma iff_to_and : forall A B : SProp, (A <-> B) <-> (A -> B) /\ (B -> A).
Proof.
  intros; split; intros [Hl Hr]; (split; intros; [ apply Hl | apply Hr]); assumption.
Qed.

(** * First-order quantifiers *)

(** [ex P], or simply [exists x, P x], or also [exists x:A, P x],
    expresses the existence of an [x] of some type [A] in [Set] which
    satisfies the predicate [P].  This is existential quantification.

    [ex2 P Q], or simply [exists2 x, P x & Q x], or also
    [exists2 x:A, P x & Q x], expresses the existence of an [x] of
    type [A] which satisfies both predicates [P] and [Q].

    Universal quantification is primitively written [forall x:A, Q]. By
    symmetry with existential quantification, the construction [all P]
    is provided too.
*)

Polymorphic Inductive sig@{s s' s''|u v| } (A:Type@{s|u}) (P:A -> Type@{s'|v}) :
  Type@{s''|max(u,v)} :=
    exist : forall x:A, P x -> sig P.

Definition ex@{s|u| } (A:Type@{s|u}) (P:A -> SProp) := sig@{s _ SProp|u Set} P.

Notation ex_intro := exist.

Register ex as core.ex.type.
Register ex_intro as core.ex.intro.

Section Projections.

  Variables (A:SProp) (P:A->SProp).

  Definition ex_proj1 (x:ex P) : A :=
    match x with ex_intro _ a _ => a end.

  Definition ex_proj2 (x:ex P) : P (ex_proj1 x) :=
    match x as x0 return P (ex_proj1 x0) with ex_intro _ _ b => b end.

  Register ex_proj1 as core.ex.proj1.
  Register ex_proj2 as core.ex.proj2.

End Projections.

Polymorphic Inductive sig2@{s s' s''|u v v'| } (A:Type@{s|u})
(P :A -> Type@{s'|v}) (Q :A -> Type@{s'|v'}) : Type@{s''|max(u,v,v')} :=
  exist2 : forall x:A, P x -> Q x -> sig2 P Q.

Definition ex2@{s|u| } (A:Type@{s|u}) (P Q:A -> SProp) := sig2@{s _ SProp|u Set Set} P Q.

Notation ex_intro2 := exist2.

(** [ex2] of a predicate can be projected to an [ex].

    This allows [ex_proj1] and [ex_proj2] to be usable with [ex2].

    We have two choices here: either we can set up the definition so
    that [ex_proj1] of a coerced [X : ex2 P Q] will unify with [let
    (a, _, _) := X in a] by restricting the first argument of [ex2] to
    be a [SProp], or we can define a more general [ex_of_ex2] which
    does not satisfy this conversion rule.  We choose the former,
    under the assumption that there is no reason to turn an [ex2] into
    an [ex] unless it is to project out the components. *)

Definition ex_of_ex2 (A : SProp) (P Q : A -> SProp) (X : ex2 P Q) : ex P
  := ex_intro P
              (let (a, _, _) := X in a)
              (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

Section ex2_Projections.

  Variables (A:SProp) (P Q:A->SProp).

  Definition ex_proj3 (x:ex2 P Q) : Q (ex_proj1 (ex_of_ex2 x)) :=
    match x as x0 return Q  (ex_proj1 (ex_of_ex2 x0)) with ex_intro2 _ _ x0 _ b => b end.

End ex2_Projections.

Definition all (A:Type) (P:A -> SProp) := forall x:A, P x.

(* Rule order is important to give printing priority to fully typed exists *)

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x name, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x name, A at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  A ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

Notation "'exists2' ' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x strict pattern, p at level 200, right associativity) : type_scope.
Notation "'exists2' ' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x strict pattern, A at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' ' x  :  A ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

(** Derived rules for universal quantification *)

Section universal_quantification.

  Variable A : Type.
  Variable P : A -> SProp.

  Theorem inst : forall x:A, all (fun x => P x) -> P x.
  Proof.
    unfold all; auto.
  Qed.

  Theorem gen : forall (B:SProp) (f:forall y:A, B -> P y), B -> all P.
  Proof.
    red; auto.
  Qed.

End universal_quantification.

(** * Equality *)

Unset Implicit Arguments.

(* The observational equality *)

Inductive obseq@{u} (A : Type@{u}) (a : A) : forall (b : A), SProp :=
| obseq_refl : obseq A a a.
Notation "a ~ b" := (obseq _ a b) (at level 50).

Arguments obseq {A} a _.
Arguments obseq_refl {A a} , [A] a.

Definition obseq_trans {A : Type} {a b c : A} (e : a ~ b) (e' : b ~ c) : a ~ c :=
  obseq_sind _ b (fun X _ => a ~ X) e c e'.
Notation "e @@@ f" := (obseq_trans e f) (at level 40, left associativity, only parsing).

(* The equality on the universe is annoying, because it needs a superfluous universe level.
   The other option is to have a second observational equality exclusively for universes: *)
Inductive obseqU@{u} (A : Type@{u}) : Type@{u} -> SProp :=
| obseqU_refl : obseqU A A.

(* Type casting *)
(* cast has two universe parameters because we use obseq instead of obseqU *)

Symbol cast@{u v} : forall (A B : Type@{u}), @obseq@{v} Type@{u} A B -> A -> B.
Notation "e # a" := (cast _ _ e a) (at level 55, only parsing).

(* SSProp casting *)
(* We do not want to use sort polymorphism for cast, to avoid useless (and potentially looping)
   computations in SSProp *)

Definition cast_prop (A B : SProp) (e : A ~ B) (a : A) := obseq_sind SProp A (fun X _ => X) a B e.
Notation "e #% a" := (cast_prop _ _ e a) (at level 40, only parsing).

Rewrite Rule cast_refl :=
| cast ?A ?A _ ?t ==> ?t.

(* We can use cast to derive large elimination principles for obseq *)

Definition ap {A B} (f : A -> B) {x y} (e : x ~ y) : f x ~ f y :=
  obseq_sind _ x (fun y _ => f x ~ f y) obseq_refl _ e.

Definition apd {A} {a} (P : forall b : A, a ~ b -> Type) (b : A) (e : a ~ b) : P a obseq_refl ~ P b e :=
  obseq_sind _ a (fun b e => P a obseq_refl ~ P b e) obseq_refl b e.

Definition obseq_rect@{u v v'} : forall (A : Type@{u}) (a : A) (P : forall b : A, obseq@{u} a b -> Type@{v}),
    P a obseq_refl@{u} -> forall (b : A) (e : obseq@{u} a b), P b e :=
  fun A a P t b e => cast@{v v'} (P a obseq_refl) (P b e) (apd P b e) t.

Definition obseq_rec@{u v} : forall (A : Type@{u}) (a : A) (P : forall b : A, obseq@{u} a b -> Set),
    P a obseq_refl@{u} -> forall (b : A) (e : obseq@{u} a b), P b e :=
  fun A a P t b e => cast@{Set v} (P a obseq_refl) (P b e) (apd P b e) t.

(* The SProp eliminator is an axiom.
   The observational equality should not be used with SProp anyway. *)
Parameter obseq_ind@{u} : forall (A : Type@{u}) (a : A) (P : forall b : A, obseq@{u} a b -> SProp),
   P a obseq_refl@{u} -> forall (b : A) (e : obseq@{u} a b), P b e.

(** Definition of the observational equality on pi's *)

Parameter obseq_forall_1 : forall {A A' B B'}, (forall (x : A), B x) ~ (forall (x : A'), B' x) -> A' ~ A.
Parameter obseq_forall_2 : forall {A A' B B'} (e : (forall (x : A), B x) ~ (forall (x : A'), B' x)) (x : A'),
    B (obseq_forall_1 e # x) ~ B' x.

Parameter funext : forall {A B} (f g : forall (x : A), B x), (forall (x : A), f x ~ g x) -> f ~ g.

Rewrite Rule cast_pi :=
| @{|u v+|+} |- cast@{u v} (forall (x : ?A), ?B) (forall (x : ?A'), ?B') ?e ?f
   ==> fun (x : ?A') => cast ?B@{x := cast ?A' ?A (obseq_forall_1@{v u u u u u v} ?e) x}
                             ?B'@{x := x}
                             (obseq_forall_2@{u u u u u v u v v} ?e x)
                             (?f (cast ?A' ?A (obseq_forall_1@{v u u u u u v} ?e) x)).

Set Implicit Arguments.

(** [eq x y], or simply [x=y] expresses the equality of [x] and
    [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others SProperties (symmetry, transitivity, replacement of
    equals by equals) are proved below. The type of [x] and [y] can be
    made explicit using the notation [x = y :> A]. This is Leibniz equality
    as it expresses that [x] and [y] are equal iff every SProperty on
    [A] which is true of [x] is also true of [y] *)

(*
Inductive eq (A:Type) (x:A) : A -> SProp :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.
 *)

Notation "x = y :> A" := (@obseq A x y) : type_scope.

Arguments obseq_rec [A] x P _ y _ : rename.
Arguments obseq_rect [A] x P _ y _ : rename.

Notation "x = y" := (obseq x y) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

#[global]
Hint Resolve I conj or_introl or_intror : core.

#[global]
Hint Resolve obseq_refl : core.

#[global]
Hint Resolve ex_intro ex_intro2: core.

Definition eq_rect : forall [A : Type] (x : A) (P : A -> Type),
P x -> forall a : A, x = a -> P a := fun A x P => @obseq_rect A x (fun a _ => P a).

Definition eq_sind : forall [A : Type] (x : A) (P : A -> SProp),
P x -> forall a : A, x = a -> P a := fun A x P => @obseq_sind A x (fun a _ => P a).

Arguments eq_rect [A] x P _ y _ : rename.

Register obseq as core.eq.type.
Register obseq_refl as core.eq.refl.
Register obseq_ind as core.eq.ind.
Register eq_sind as core.eq.sind.
Register eq_rect as core.eq.rect.

Section Logic_lemmas.

  Theorem absurd : forall A C:SProp, A -> ~ A -> C.
  Proof.
    unfold not; intros A C h1 h2.
    destruct (h2 h1).
  Qed.

  Section equality.
    Variables A B : Type.
    Variable f : A -> B.
    Variables x y z : A.

    Theorem eq_sym : x = y -> y = x.
    Proof.
      destruct 1; reflexivity.
    Defined.

    Register eq_sym as core.eq.sym.

    Theorem eq_trans : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Register eq_trans as core.eq.trans.

    Theorem eq_trans_r : x = y -> z = y -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Theorem f_equal : x = y -> f x = f y.
    Proof.
      destruct 1; reflexivity.
    Defined.

    Register f_equal as core.eq.congr.

    Theorem not_eq_sym : x <> y -> y <> x.
    Proof.
      red. intros h1 h2; apply h1; destruct h2; reflexivity.
    Qed.

  End equality.

  Definition eq_sind_r :
    forall (A:Type) (x:A) (P:A -> SProp), P x -> forall y:A, y = x -> P y.
  Proof.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Register eq_sind_r as core.eq.sind_r.

  Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> SProp), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Register eq_ind_r as core.eq.ind_r.

  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rect_r :
    forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.
End Logic_lemmas.

Module EqNotations.
  Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  H  in  '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  H  in  '/' H' ']'").
  Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' -> H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' -> [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10, only parsing).

  Notation "'rew' 'dependent' H 'in' H'"
    := (obseq_rect _ _ H' _ H)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> H 'in' H'"
    := (obseq_rect _ _ H' _ H)
         (at level 10, H' at level 10, only parsing).
  Notation "'rew' 'dependent' <- H 'in' H'"
    := (obseq_rect _ _ H' _ (eq_sym H))
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ 'fun' y p => P ] H 'in' H'"
    := (obseq_rect _ (fun y p => P) H' _ H)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ 'fun' y p => P ] H 'in' H'"
    := (obseq_rect _ (fun y p => P) H' _ H)
         (at level 10, H' at level 10, y name, p name, only parsing).
  Notation "'rew' 'dependent' <- [ 'fun' y p => P ] H 'in' H'"
    := (obseq_rect _ (fun y p => P) H' _ (eq_sym H))
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  <-  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ P ] H 'in' H'"
    := (obseq_rect _ P H' _ H)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ P ] H 'in' H'"
    := (obseq_rect _ P H' _ H)
         (at level 10, H' at level 10,
          only parsing).
  Notation "'rew' 'dependent' <- [ P ] H 'in' H'"
    := (obseq_rect _ P H' _ (eq_sym H))
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  [ P ]  '/    ' H  in  '/' H' ']'").

 End EqNotations.

Import EqNotations.

Section equality_dep.
  Variable A : Type.
  Variable B : A -> Type.
  Variable f : forall x, B x.
  Variables x y : A.

  Theorem f_equal_dep (H: x = y) : rew H in f x = f y.
  Proof.
    destruct H; reflexivity.
  Defined.

End equality_dep.

Lemma f_equal_dep2 {A A' B B'} (f : A -> A') (g : forall a:A, B a -> B' (f a))
  {x1 x2 : A} {y1 : B x1} {y2 : B x2} (H : x1 = x2) :
  rew H in y1 = y2 -> rew f_equal f H in g x1 y1 = g x2 y2.
Proof.
  destruct H, 1. reflexivity.
Defined.

Lemma rew_opp_r A (P:A->Type) (x y:A) (H:x=y) (a:P y) : rew H in rew <- H in a = a.
Proof.
destruct H.
reflexivity.
Defined.

Lemma rew_opp_l A (P:A->Type) (x y:A) (H:x=y) (a:P x) : rew <- H in rew H in a = a.
Proof.
destruct H.
reflexivity.
Defined.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.

Register f_equal2 as core.eq.congr2.

Theorem f_equal3 :
  forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1)
    (x2 y2:A2) (x3 y3:A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof.
  destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal4 :
  forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal5 :
  forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

(*
Theorem f_equal_compose A B C (a b:A) (f:A->B) (g:B->C) (e:a=b) :
  f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e.
Proof.
  destruct e. reflexivity.
Defined.
*)

(** The groupoid structure of equality *)

(*
Theorem eq_trans_refl_l A (x y:A) (e:x=y) : eq_trans eq_refl e = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_trans_refl_r A (x y:A) (e:x=y) : eq_trans e eq_refl = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_sym_involutive A (x y:A) (e:x=y) : eq_sym (eq_sym e) = e.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_l A (x y:A) (e:x=y) : eq_trans (eq_sym e) e = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_r A (x y:A) (e:x=y) : eq_trans e (eq_sym e) = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_assoc A (x y z t:A) (e:x=y) (e':y=z) (e'':z=t) :
  eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
Proof.
  destruct e''; reflexivity.
Defined.
*)

Theorem rew_map A B (P:B->Type) (f:A->B) x1 x2 (H:x1=x2) (y:P (f x1)) :
  rew [fun x => P (f x)] H in y = rew f_equal f H in y.
Proof.
  destruct H; reflexivity.
Defined.

Theorem eq_trans_map {A B} {x1 x2 x3:A} {y1:B x1} {y2:B x2} {y3:B x3}
  (H1:x1=x2) (H2:x2=x3) (H1': rew H1 in y1 = y2) (H2': rew H2 in y2 = y3) :
  rew eq_trans H1 H2 in y1 = y3.
Proof.
  destruct H2. exact (eq_trans H1' H2').
Defined.

Lemma map_subst {A} {P Q:A->Type} (f : forall x, P x -> Q x) {x y} (H:x=y) (z:P x) :
  rew H in f x z = f y (rew H in z).
Proof.
  destruct H. reflexivity.
Defined.

Lemma map_subst_map {A B} {P:A->Type} {Q:B->Type} (f:A->B) (g : forall x, P x -> Q (f x))
  {x y} (H:x=y) (z:P x) :
  rew f_equal f H in g x z = g y (rew H in z).
Proof.
  destruct H. reflexivity.
Defined.

Lemma rew_swap A (P:A->Type) x1 x2 (H:x1=x2) (y1:P x1) (y2:P x2) : rew H in y1 = y2 -> y1 = rew <- H in y2.
Proof.
  destruct H. trivial.
Defined.

Lemma rew_compose A (P:A->Type) x1 x2 x3 (H1:x1=x2) (H2:x2=x3) (y:P x1) :
  rew H2 in rew H1 in y = rew (eq_trans H1 H2) in y.
Proof.
  destruct H2. reflexivity.
Defined.

(** Extra SProperties of equality *)

(* Theorem eq_id_comm_l A (f:A->A) (Hf:forall a, a = f a) a : f_equal f (Hf a) = Hf (f a).
Proof.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf a)).
  destruct (Hf a) at 1 2.
  destruct (Hf a).
  reflexivity.
Defined.

Theorem eq_id_comm_r A (f:A->A) (Hf:forall a, f a = a) a : f_equal f (Hf a) = Hf (f a).
Proof.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf (f (f a)))).
  set (Hfsymf := fun a => eq_sym (Hf a)).
  change (eq_sym (Hf (f (f a)))) with (Hfsymf (f (f a))).
  pattern (Hfsymf (f (f a))).
  destruct (eq_id_comm_l f Hfsymf (f a)).
  destruct (eq_id_comm_l f Hfsymf a).
  unfold Hfsymf.
  destruct (Hf a). simpl.
  rewrite eq_trans_refl_l.
  reflexivity.
Defined.

Lemma eq_refl_map_distr A B x (f:A->B) : f_equal f (eq_refl x) = eq_refl (f x).
Proof.
  reflexivity.
Qed.

Lemma eq_trans_map_distr A B x y z (f:A->B) (e:x=y) (e':y=z) : f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').
Proof.
destruct e'.
reflexivity.
Defined.

Lemma eq_sym_map_distr A B (x y:A) (f:A->B) (e:x=y) : eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
destruct e.
reflexivity.
Defined.

Lemma eq_trans_sym_distr A (x y z:A) (e:x=y) (e':y=z) : eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).
Proof.
destruct e, e'.
reflexivity.
Defined.
*)

Lemma eq_trans_rew_distr A (P:A -> Type) (x y z:A) (e:x=y) (e':y=z) (k:P x) :
    rew (eq_trans e e') in k = rew e' in rew e in k.
Proof.
  destruct e, e'; reflexivity.
Qed.

Lemma rew_const A P (x y:A) (e:x=y) (k:P) :
    rew [fun _ => P] e in k = k.
Proof.
  destruct e; reflexivity.
Qed.

(* Aliases *)

Notation sym_eq := eq_sym (only parsing).
Notation trans_eq := eq_trans (only parsing).
Notation sym_not_eq := not_eq_sym (only parsing).

Notation refl_equal := obseq_refl (only parsing).
Notation sym_equal := eq_sym (only parsing).
Notation trans_equal := eq_trans (only parsing).
Notation sym_not_equal := not_eq_sym (only parsing).

#[global]
Hint Immediate eq_sym not_eq_sym: core.

(** Basic definitions about relations and SProperties *)

Definition subrelation (A B : Type) (R R' : A->B->SProp) :=
  forall x y, R x y -> R' x y.

Definition unique (A : Type) (P : A->SProp) (x:A) :=
  P x /\ forall (x':A), P x' -> x=x'.

Definition uniqueness (A:Type) (P:A->SProp) := forall x y, P x -> P y -> x = y.

(** Unique existence *)

Notation "'exists' ! x .. y , p" :=
  (ex (unique (fun x => .. (ex (unique (fun y => p))) ..)))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  !  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Lemma unique_existence : forall (A:Type) (P:A->SProp),
  ((exists x, P x) /\ uniqueness P) <-> (exists! x, P x).
Proof.
  intros A P; split.
  - intros ((x,Hx),Huni); exists x; red; auto.
  - intros (x,(Hx,Huni)); split.
    + exists x; assumption.
    + intros x' x'' Hx' Hx''; transitivity x.
      * symmetry; auto.
      * auto.
Qed.

Lemma forall_exists_unique_domain_coincide :
  forall A (P:A->SProp), (exists! x, P x) ->
  forall Q:A->SProp, (forall x, P x -> Q x) <-> (exists x, P x /\ Q x).
Proof.
  intros A P (x & Hp & Huniq); split.
  - intro; exists x; auto.
  - intros (x0 & HPx0 & HQx0) x1 HPx1.
    assert (H : x0 = x1) by (transitivity x; [symmetry|]; auto).
    destruct H.
    assumption.
Qed.

Lemma forall_exists_coincide_unique_domain :
  forall A (P:A->SProp),
  (forall Q:A->SProp, (forall x, P x -> Q x) <-> (exists x, P x /\ Q x))
  -> (exists! x, P x).
Proof.
  intros A P H.
  destruct (H P) as ((x & Hx & _),_); [trivial|].
  exists x. split; [trivial|].
  destruct (H (fun x'=>x=x')) as (_,Huniq).
  apply Huniq. exists x; auto.
Qed.

(** * Being inhabited *)

(** The predicate [inhabited] can be used in different contexts. If [A] is
    thought as a type, [inhabited A] states that [A] is inhabited. If [A] is
    thought as a computationally relevant SProposition, then
    [inhabited A] weakens [A] so as to hide its computational meaning.
    The so-weakened proof remains computationally relevant but only in
    a SPropositional context.
*)

Inductive inhabited (A:Type) : SProp := inhabits : A -> inhabited A.

#[global]
Hint Resolve inhabits: core.

Lemma exists_inhabited : forall (A:Type) (P:A->SProp),
  (exists x, P x) -> inhabited A.
Proof.
  destruct 1; auto.
Qed.

Lemma inhabited_covariant (A B : Type) : (A -> B) -> inhabited A -> inhabited B.
Proof.
  intros f [x];exact (inhabits (f x)).
Qed.

(** Declaration of stepl and stepr for eq and iff *)

Lemma eq_stepl : forall (A : Type) (x y z : A), x = y -> x = z -> z = y.
Proof.
  intros A x y z H1 H2. rewrite <- H2; exact H1.
Qed.

Declare Left Step eq_stepl.
Declare Right Step eq_trans.

Lemma iff_stepl : forall A B C : SProp, (A <-> B) -> (A <-> C) -> (C <-> B).
Proof.
  intros ? ? ? [? ?] [? ?]; split; intros; auto.
Qed.

Declare Left Step iff_stepl.
Declare Right Step iff_trans.


(** Equality for [ex] *)
(* Section ex.
  Local Unset Implicit Arguments.
 *)  (** Projecting an equality of a pair to equality of the first components *)

  (* This is not true anymore  *)
(*   Definition ex_proj1_eq {A : SProp} {P : A -> SProp} {u v : exists a : A, P a} (p : u = v)
    : ex_proj1 u = ex_proj1 v
    := f_equal (@ex_proj1 _ _) p.
 *)
  (** Projecting an equality of a pair to equality of the second components *)
(*   Definition ex_proj2_eq {A : SProp} {P : A -> SProp} {u v : exists a : A, P a} (p : u = v)
    : rew ex_proj1_eq p in ex_proj2 u = ex_proj2 v
    := rew dependent p in eq_refl.
 *)

 (*
Section ex2_SProp.
  Variables (A:SProp) (P Q:A->SProp).

  Definition ex2_rect (P0 : ex2 P Q -> Type) (f : forall x p q, P0 (ex_intro2 P Q x p q))
    : forall e, P0 e.
    intros e. eapply f.  destruct e.
    := fun e => f _ _ _.
  Definition ex2_rec : forall (P0 : ex2 P Q -> Set) (f : forall x p q, P0 (ex_intro2 P Q x p q)),
      forall e, P0 e
    := ex2_rect.

End ex2_SProp.
*)
