(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Basic specifications : sets that may contain logical information *)

Set Implicit Arguments.
Set Reversible Pattern Implicit.

Set Observational Inductives.
Set Universe Polymorphism.

Require Import Notations.
Require Import Ltac.
Require Import Datatypes.
Require Import Logic.

(** Subsets and Sigma-types *)

(** [(sig A P)], or more suggestively [{x:A | P x}], denotes the subset
    of elements of the type [A] which satisfy the predicate [P].
    Similarly [(sig2 A P Q)], or [{x:A | P x & Q x}], denotes the subset
    of elements of the type [A] which satisfy both [P] and [Q]. *)

Definition sigP_rect@{s s' s''| u u' u''|} :
  forall [A : Type@{s|u}] [P : A -> Type@{s'|u'}]
    (P0 : sigP P -> Type@{s''|u''}),
    (forall (x : A) (p : P x), P0 (existP P x p)) -> forall s : sigP P, P0 s :=
  fun A P P0 f s =>
    match s as s0 return (P0 s0) with
          | existP _ x p => f x p
    end.

Register sigP as core.sigP.type.
Register existP as core.sigP.intro.
Register sigP_rect as core.sigP.rect.

Definition sig@{u} := sigP@{Type SProp Type | u Set}.
Notation exist := existP.
Definition sig_rect@{u u'} := sigP_rect@{Type SProp Type | u Set u'}.

Register sig as core.sig.type.
Register exist as core.sig.intro.
Register sig_rect as core.sig.rect.

Definition sig2P_rect@{s s' s''| u u' v' u''|} :
  forall [A : Type@{s|u}] [P : A -> Type@{s'|u'}]
    [Q : A -> Type@{s'|v'}]
    (P0 : sig2P P Q -> Type@{s''|u''}),
    (forall (x : A) (p : P x) (q : Q x), P0 (exist2P P Q x p q)) ->
    forall s : sig2P P Q, P0 s :=
  fun A P Q P0 f s =>
    match s as s0 return (P0 s0) with
          | exist2P _ _ x y p => f x y p
    end.

(* Notations *)

Definition sig2@{u} := sig2P@{Type SProp Type | u Set Set}.
Notation exist2 := exist2P.
Definition sig2_rect@{u u'} := sig2P_rect@{Type SProp Type | u Set Set u'}.

Arguments sig (A P)%_type.
Arguments sig2 (A P Q)%_type.

Definition sigT (A:Type) (P:A -> Type) : Type := @sigP A P.
Notation existT := existP.
Definition sigT_rect@{u u' u''} := sigP_rect@{Type Type Type | u u' u''}.

Definition sigT2 (A:Type) (P Q:A -> Type) : Type := @sig2P A P Q.
Notation existT2 := exist2P.
Definition sigT2_rect@{u u' v' u''} := sig2P_rect@{Type Type Type | u u' v' u''}.

Register sigT as core.sigT.type.
Register existT as core.sigT.intro.
Register sigT_rect as core.sigT.rect.

Notation "{ x & P }" := (sigP (fun x => P)) : type_scope.
Notation "{ x & P & Q }" := (sig2P (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A & P }" := (sigP (A:=A) (fun x => P)) : type_scope.
Notation "{ x : A & P & Q }" := (sig2P (A:=A) (fun x => P) (fun x => Q)) :
  type_scope.

Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
Notation "{ x | P & Q }" := (sig2 (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A | P }" := (sig (A:=A) (fun x => P)) : type_scope.
Notation "{ x : A | P & Q }" := (sig2 (A:=A) (fun x => P) (fun x => Q)) :
  type_scope.

Notation "{ ' pat & P }" := (sigP (fun pat => P)) : type_scope.
Notation "{ ' pat & P & Q }" := (sig2P (fun pat => P) (fun pat => Q)) : type_scope.
Notation "{ ' pat : A & P }" := (sigP (A:=A) (fun pat => P)) : type_scope.
Notation "{ ' pat : A & P & Q }" := (sig2P (A:=A) (fun pat => P) (fun pat => Q)) :
  type_scope.

Notation "{ ' pat | P }" := (sig (fun pat => P)) : type_scope.
Notation "{ ' pat | P & Q }" := (sig2 (fun pat => P) (fun pat => Q)) : type_scope.
Notation "{ ' pat : A | P }" := (sig (A:=A) (fun pat => P)) : type_scope.
Notation "{ ' pat : A | P & Q }" := (sig2 (A:=A) (fun pat => P) (fun pat => Q)) :
  type_scope.

Add Printing Let sigP.
Add Printing Let sig2P.

(** Projections of [sig]

    An element [y] of a subset [{x:A | (P x)}] is the pair of an [a]
    of type [A] and of a proof [h] that [a] satisfies [P].  Then
    [(proj1_sig y)] is the witness [a] and [(proj2_sig y)] is the
    proof of [(P a)] *)

Definition proj1_sig@{s s'|u v| } (A:Type@{s|u}) (P:A -> Type@{s'|v})
     (e:sigP@{_ _ s|_ _} P) := match e with
                                    | exist _ a b => a
                                    end.

Definition proj2_sig@{s|u v| } (A:Type@{s|u}) (P:A -> Type@{s|v})
    (e:sigP P) :=
    match e return P (proj1_sig e) with
    | exist _ a b => b
    end.

Section Subset_projections.

  Definition proj2_SProp_sig (A:Type) (P:A -> SProp)
    (e:sig P) :=
    match e return P (proj1_sig e) with
    | exist _ a b => b
    end.

  Register proj1_sig as core.sig.proj1.
  Register proj2_sig as core.sig.proj2.
  Register proj2_SProp_sig as core.sig.proj2S.

End Subset_projections.


(** [sig2] of a predicate can be projected to a [sig].

    This allows [proj1_sig] and [proj2_sig] to be usable with [sig2].

    The [let] statements occur in the body of the [exist] so that
    [proj1_sig] of a coerced [X : sig2 P Q] will unify with [let (a,
    _, _) := X in a] *)

Definition sig_of_sig2@{s s' s''| u v v' v''|u <= v'', v <= v''}
  (A : Type@{s|u}) (P :A -> Type@{s'|v}) (Q :A -> Type@{s'|v'})
  (X : sig2P@{s s' s''|u v v'} P Q) : sigP@{s s' s''|u v} P :=
  match X with exist2 _ _ a p q => exist P a p end.

Definition proj3_sig@{s|u v v' v''|u <= v'', v <= v''} (A:Type@{s|u})
    (P:A -> Type@{s|v}) (Q:A -> Type@{s|v'})
    (e:sig2P P Q) :=
    let (a, b, c) return Q (proj1_sig (sig_of_sig2 e)) := e in c.

(** Projections of [sig2]

    An element [y] of a subset [{x:A | (P x) & (Q x)}] is the triple
    of an [a] of type [A], a of a proof [h] that [a] satisfies [P],
    and a proof [h'] that [a] satisfies [Q].  Then
    [(proj1_sig (sig_of_sig2 y))] is the witness [a],
    [(proj2_sig (sig_of_sig2 y))] is the proof of [(P a)], and
    [(proj3_sig y)] is the proof of [(Q a)]. *)

Section Subset_projections2.

  Variable A : Type.
  Variables P Q : A -> SProp.

  Definition proj3_SProp_sig (e : sig2 P Q) :=
    let (a, b, c) return Q (proj1_sig (sig_of_sig2 e)) := e in c.

End Subset_projections2.

Module SigNotations.
  Notation "( x ; y )" := (exist _ x y) (at level 0, format "( x ;  '/  ' y )").
  Notation "x .1" := (proj1_sig x) (at level 1, left associativity, format "x .1").
  Notation "x .2" := (proj2_sig x) (at level 1, left associativity, format "x .2").
End SigNotations.

Import SigNotations.

Local Notation "x .3" := (proj3_sig x) (at level 1, left associativity, format "x .3").

(* sanity check *)
Definition ex_of_sig (A : Type) (P : A -> SProp) (X : sig P) : ex P
  := ex_intro P (proj1_sig X) (proj2_SProp_sig X).

Definition ex2_of_sig2 (A : Type) (P Q : A -> SProp) (X : sig2 P Q) : ex2 P Q
  := ex_intro2 P Q (proj1_sig (sig_of_sig2 X)) (proj2_SProp_sig (sig_of_sig2 X)) (proj3_SProp_sig X).

Notation projT1 := proj1_sig.
Notation projT2 := proj2_sig.
Notation projT3 := proj3_sig.

(** η Principles *)
Definition sig_eta {A P} (p : { a : A & P a })
  : p = exist _ (projT1 p) (projT2 p).
Proof. destruct p; reflexivity. Defined.

Definition sig2_eta {A P Q} (p : { a : A & P a & Q a })
  : p = exist2 _ _ (projT1 (sig_of_sig2 p)) (projT2 (sig_of_sig2 p)) (projT3 p).
Proof. destruct p; reflexivity. Defined.

(** [exists x : A, B] is equivalent to [inhabited {x : A | B}] *)
Lemma exists_to_inhabited_sig {A P} : (exists x : A, P x) -> inhabited {x : A | P x}.
Proof.
  intros [x y]. exact (inhabits (exist _ x y)).
Qed.

Lemma inhabited_sig_to_exists {A P} : inhabited {x : A | P x} -> exists x : A, P x.
Proof.
  intros [[x y]];exists x;exact y.
Qed.

(** Subtyping for prod *)

Section ProdSigT.

  Variable A B : Type.

  Definition sigT_of_prod (p : A * B) := (fst p; snd p).
  Definition prod_of_sigT (s : { _ : A & B }) := (s.1, s.2).

  Lemma sigT_prod_sigT p : sigT_of_prod (prod_of_sigT p) = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma prod_sigT_prod s : prod_of_sigT (sigT_of_prod s) = s.
  Proof. destruct s; reflexivity. Qed.

End ProdSigT.

(** Equality of sigma types *)

Import EqNotations.

(** Equality for [sigT] *)
Section sigT.
  Local Unset Implicit Arguments.
  (** Projecting an equality of a pair to equality of the first components *)
  Definition projT1_eq@{s' | u v v' | u <= v', v <= v'} {A:Type@{u}} {P : A -> Type@{s' | v}} {u v : { a : A & P a }} (p : u = v)
    : u.1 = v.1
    := f_equal (fun x => x.1) p.

    (*cannot unify "rew [fun a : A => P a] projT1_eq obseq_refl in projT2 u" and "projT2 u"*)
  Definition projT2_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
    : rew projT1_eq p in u.2 = v.2.
    destruct p; reflexivity.
  Qed.

  (** Equality of [sigT] is itself a [sigT] (forwards-reasoning version) *)
  Definition eq_existT_uncurried {A : Type} {P : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : { p : u1 = v1 & rew p in u2 = v2 } : SProp)
    : (u1; u2) = (v1; v2).
  Proof.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  (** Equality of [sigT] is itself a [sigT] (backwards-reasoning version) *)
  Definition eq_sigT_uncurried {A : Type} {P : A -> Type} (u v : { a : A & P a })
             (pq : { p : u.1 = v.1 & rew p in u.2 = v.2 } : SProp)
    : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    apply eq_existT_uncurried; exact pq.
  Defined.

  Lemma eq_existT_curried {A : Type} {P : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (p : u1 = v1) (q : rew p in u2 = v2) : (u1; u2) = (v1; v2).
  Proof.
    apply eq_sigT_uncurried; exists p; exact q.
  Defined.


  (** Curried version of proving equality of sigma types *)
  Definition eq_sigT {A : Type} {P : A -> Type} (u v : { a : A & P a })
             (p : u.1 = v.1) (q : rew p in u.2 = v.2)
    : u = v
    := eq_sigT_uncurried u v (existT _ p q).

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_existT_l {A : Type} {P : A -> Type} {u1 : A} {u2 : P u1} {v : { a : A & P a }}
             (p : u1 = v.1) (q : rew p in u2 = v.2) : (u1; u2) = v
    := eq_sigT (u1; u2) v p q.
  Definition eq_existT_r {A : Type} {P : A -> Type} {u : { a : A & P a }} {v1 : A} {v2 : P v1}
             (p : u.1 = v1) (q : rew p in u.2 = v2) : u = (v1; v2)
    := eq_sigT u (v1; v2) p q.

  (** Equality of [sigT] when the property is an hProp *)
  Definition eq_sigT_hprop {A P} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : { a : A & P a })
             (p : u.1 = v.1)
    : u = v
    := eq_sigT u v p (P_hprop _ _ _).

  (** Equivalence of equality of [sigT] with a [sigT] of equality *)
  (** We could actually prove an isomorphism here, and not just [<->],
      but for simplicity, we don't. *)
  Definition eq_sigT_uncurried_iff {A P}
             (u v : { a : A & P a })
    : u = v <-> { p : u.1 = v.1 & rew p in u.2 = v.2 }.
  Proof.
    split; [ intro; subst; exists obseq_refl; reflexivity | apply eq_sigT_uncurried].
  Qed.

  (** Induction principle for [@eq (sigT _)] *)
  Definition eq_sigT_rect {A P} {u v : { a : A & P a }} (Q : u = v -> Type)
             (f : forall p q, Q (eq_sigT u v p q))
    : forall p, Q p.
  Proof. intro p; specialize (f (projT1_eq p) (projT2_eq p)). induction u. induction p. exact f. Defined.

  Definition eq_sigT_rec {A P u v} (Q : u = v :> { a : A & P a } -> Set) := eq_sigT_rect Q.
  Definition eq_sigT_ind {A P u v} (Q : u = v :> { a : A & P a } -> Prop) := eq_sigT_rec Q.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_sigT_rect_existT_l {A P} {u1 u2 v} (Q : _ -> Type)
             (f : forall p q, Q (@eq_existT_l A P u1 u2 v p q))
    : forall p, Q p
    := eq_sigT_rect Q f.
  Definition eq_sigT_rect_existT_r {A P} {u v1 v2} (Q : _ -> Type)
             (f : forall p q, Q (@eq_existT_r A P u v1 v2 p q))
    : forall p, Q p
    := eq_sigT_rect Q f.
  Definition eq_sigT_rect_existT {A P} {u1 u2 v1 v2} (Q : _ -> Type)
             (f : forall p q, Q (@eq_existT_curried A P u1 v1 u2 v2 p q))
    : forall p, Q p
    := eq_sigT_rect Q f.

  (** We want uncurried versions so [inversion_sigma] can accept
      intropatterns, but we use [ex] types for the induction
      hypothesis to avoid extraction errors about informative
      inductive types having Prop instances *)
  Definition eq_sigT_rect_uncurried {A P} {u v : { a : A & P a }} (Q : u = v -> Type)
             (f : forall pq : exists p : u.1 = v.1, _, Q (eq_sigT u v (ex_proj1 pq) (ex_proj2 pq)))
    : forall p, Q p
    := eq_sigT_rect Q (fun p q => f (ex_intro _ p q)).
  Definition eq_sigT_rec_uncurried {A P u v} (Q : u = v :> { a : A & P a } -> Set) := eq_sigT_rect_uncurried Q.
  Definition eq_sigT_ind_uncurried {A P u v} (Q : u = v :> { a : A & P a } -> Prop) := eq_sigT_rec_uncurried Q.

  (** Equivalence of equality of [sigT] involving hProps with equality of the first components *)
  Definition eq_sigT_hprop_iff {A P} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : { a : A & P a })
    : u = v <-> (u.1 = v.1)
    := conj (fun p => f_equal (@projT1 _ _) p) (eq_sigT_hprop P_hprop u v).

  (** Non-dependent classification of equality of [sigT] *)
  Definition eq_sigT_nondep {A B : Type} (u v : { a : A & B })
             (p : u.1 = v.1) (q : u.2 = v.2)
    : u = v
    := @eq_sigT _ _ u v p (eq_trans (rew_const _ _) q).

  (** Classification of transporting across an equality of [sigT]s *)
  Lemma rew_sigT {A x} {P : A -> Type} (Q : forall a, P a -> SProp) (u : { p : P x & Q x p } : Type) {y} (H : x = y)
    : rew [fun a => { p : P a & Q a p }] H in u
      = existT
          (Q y)
          (rew H in u.1)
          (srew dependent [(fun x H => Q x (rew H in u.1))] H in (proj2_SProp_sig u)).
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sigT.
Global Arguments eq_existT_curried A P _ _ _ _ !p !q / .

(** Equality for [sig] *)
Section sig.
  (** We define this as a [Let] rather than a [Definition] to avoid
      extraction errors about informative inductive types having Prop
      instances *)
  Local Unset Implicit Arguments.
  (** Projecting an equality of a pair to equality of the first components *)
  Definition proj1_sig_eq {A} {P : A -> SProp} {u v : { a : A | P a }} (p : u = v)
    : proj1_sig u = proj1_sig v
    := f_equal (@proj1_sig _ _) p.

  (** Equality of [sig] is itself a [sig] (forwards-reasoning version) *)
  Definition eq_exist_uncurried {A : Type} {P : A -> SProp} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : u1 = v1)
    : exist _ u1 u2 = exist _ v1 v2.
  Proof.
    destruct pq; reflexivity.
  Defined.

  (** Equality of [sig] is itself a [sig] (backwards-reasoning version) *)
  Definition eq_sig_uncurried {A : Type} {P : A -> SProp} (u v : { a : A | P a })
             (pq : proj1_sig u = proj1_sig v)
    : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    apply eq_exist_uncurried; exact pq.
  Defined.

  Lemma eq_exist_curried {A : Type} {P : A -> SProp} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (p : u1 = v1) : exist P u1 u2 = exist P v1 v2.
  Proof.
    apply eq_sig_uncurried; exact p.
  Defined.

  (** Curried version of proving equality of sigma types *)
  Definition eq_sig {A : Type} {P : A -> SProp} (u v : { a : A | P a })
             (p : proj1_sig u = proj1_sig v)
    : u = v
    := eq_sig_uncurried u v p.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_exist_l {A : Type} {P : A -> SProp} {u1 : A} {u2 : P u1} {v : { a : A | P a }}
             (p : u1 = proj1_sig v)  : exist _ u1 u2 = v
    := eq_sig (exist _ u1 u2) v p.
  Definition eq_exist_r {A : Type} {P : A -> SProp} {u : { a : A | P a }} {v1 : A} {v2 : P v1}
             (p : proj1_sig u = v1) : u = exist _ v1 v2
    := eq_sig u (exist _ v1 v2) p.

  (** Induction principle for [@eq (sig _)] *)
  Definition eq_sig_rect {A P} {u v : { a : A | P a }} (Q : u = v -> Type)
             (f : forall p, Q (eq_sig u v p))
    : forall p, Q p.
  Proof. intro p; exact (f (proj1_sig_eq p)). Defined.
  Definition eq_sig_rec {A P u v} (Q : u = v :> { a : A | P a } -> Set) := eq_sig_rect Q.
  Definition eq_sig_ind {A P u v} (Q : u = v :> { a : A | P a } -> Prop) := eq_sig_rec Q.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_sig_rect_exist_l {A P} {u1 u2 v} (Q : _ -> Type)
             (f : forall p, Q (@eq_exist_l A P u1 u2 v p))
    : forall p, Q p
    := eq_sig_rect Q f.
  Definition eq_sig_rect_exist_r {A P} {u v1 v2} (Q : _ -> Type)
             (f : forall p, Q (@eq_exist_r A P u v1 v2 p))
    : forall p, Q p
    := eq_sig_rect Q f.
  Definition eq_sig_rect_exist {A P} {u1 u2 v1 v2} (Q : _ -> Type)
             (f : forall p, Q (@eq_exist_curried A P u1 v1 u2 v2 p))
    : forall p, Q p
    := eq_sig_rect Q f.

  (** We want uncurried versions so [inversion_sigma] can accept
      intropatterns, but we use [ex] types for the induction
      hypothesis to avoid extraction errors about informative
      inductive types having Prop instances *)
  Definition eq_sig_rect_uncurried {A P} {u v : { a : A | P a }} (Q : u = v -> Type)
             (f : forall pq : proj1_sig u = proj1_sig v, Q (eq_sig u v pq))
    : forall p, Q p
    := eq_sig_rect Q f.
  Definition eq_sig_rec_uncurried {A P u v} (Q : u = v :> { a : A | P a } -> Set) := eq_sig_rect_uncurried Q.
  Definition eq_sig_ind_uncurried {A P u v} (Q : u = v :> { a : A | P a } -> Prop) := eq_sig_rec_uncurried Q.

  (** Equality of [sig] when the property is an hProp *)
  Definition eq_sig_hprop {A} {P : A -> SProp}
             (u v : { a : A | P a })
             (p : proj1_sig u = proj1_sig v)
    : u = v
    := eq_sig u v p.

  (** Equivalence of equality of [sig] with a [sig] of equality *)
  (** We could actually prove an isomorphism here, and not just [<->],
      but for simplicity, we don't. *)
  Definition eq_sig_uncurried_iff {A} {P : A -> SProp}
             (u v : { a : A | P a })
    : u = v <-> proj1_sig u = proj1_sig v.
  Proof.
    split; [ intro; subst; reflexivity | apply eq_sig_uncurried ].
  Defined.

  (** Equivalence of equality of [sig] involving hProps with equality of the first components *)
  Definition eq_sig_hprop_iff {A} {P : A -> SProp}
             (u v : { a : A | P a })
    : u = v <-> (proj1_sig u = proj1_sig v)
    := conj (fun p => f_equal (@proj1_sig _ _) p) (eq_sig_hprop u v).

  Lemma rew_sig {A x} {P : A -> Type} (Q : forall a, P a -> SProp) (u : { p : P x | Q x p }) {y} (H : x = y)
    : rew [fun a => { p : P a | Q a p }] H in u
      = exist
          (Q y)
          (rew H in proj1_sig u)
          (srew dependent  [(fun x H => Q x (rew H in u.1))]  H in proj2_SProp_sig u).
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sig.
Global Arguments eq_exist_curried A P _ _ _ _ !p / .

(** Equality for [sigT2] *)
Section sigT2.
  (* We make [sigT_of_sigT2] a coercion so we can use [projT1], [projT2] on [sigT2] *)
  Local Coercion sig_of_sig2 : sig2P >-> sigP.
  Local Coercion ex_of_ex2 : ex2 >-> ex.
  Local Unset Implicit Arguments.
  (** Projecting an equality of a pair to equality of the first components *)
  Definition sigT_of_sigT2_eq {A} {P Q : A -> Type} {u v : { a : A & P a & Q a }} (p : u = v)
    : u = v :> { a : A & P a }
    := f_equal _ p.
  Definition projT1_of_sigT2_eq {A} {P Q : A -> Type} {u v : { a : A & P a & Q a }} (p : u = v)
    : u.1 = v.1
    := projT1_eq (sigT_of_sigT2_eq p).

  (** Projecting an equality of a pair to equality of the second components *)
  Definition projT2_of_sigT2_eq {A} {P Q : A -> Type} {u v : { a : A & P a & Q a }} (p : u = v)
    : rew projT1_of_sigT2_eq p in u.2 = v.2.
  Proof.
    destruct p; reflexivity.
  Qed.

  (** Projecting an equality of a pair to equality of the third components *)
  Definition projT3_eq {A} {P Q : A -> Type} {u v : { a : A & P a & Q a }} (p : u = v)
    : rew projT1_of_sigT2_eq p in u.3 = v.3.
    Proof.
    destruct p; reflexivity.
  Qed.

  Notation existT2 := exist2.

  (** Equality of [sigT2] is itself a [sigT2] (forwards-reasoning version) *)
  Definition eq_existT2_uncurried {A : Type} {P Q : A -> Type}
             {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1}
             (pqr : { p : u1 = v1
                    & rew p in u2 = v2 & rew p in u3 = v3 }:SProp)
    : existT2 _ _ u1 u2 u3 = existT2 _ _ v1 v2 v3.
  Proof.
    destruct pqr as [p q r].
    destruct r, q, p; simpl.
    reflexivity.
  Defined.

  (** Equality of [sigT2] is itself a [sigT2] (backwards-reasoning version) *)
  Definition eq_sigT2_uncurried {A : Type} {P Q : A -> Type} (u v : { a : A & P a & Q a })
             (pqr : { p : u.1 = v.1
                    & rew p in u.2 = v.2 & rew p in u.3 = v.3 }: SProp)
    : u = v.
  Proof.
    destruct u as [u1 u2 u3], v as [v1 v2 v3]; simpl in *.
    apply eq_existT2_uncurried; exact pqr.
  Defined.

  Lemma eq_existT2_curried {A : Type} {P Q : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1}
             (p : u1 = v1) (q : rew p in u2 = v2) (r : rew p in u3 = v3) : existT2 P Q u1 u2 u3 = existT2 P Q v1 v2 v3.
  Proof.
    apply eq_sigT2_uncurried; exists p; exact q + exact r.
  Defined.

  (** Curried version of proving equality of sigma types *)
  Definition eq_sigT2 {A : Type} {P Q : A -> Type} (u v : { a : A & P a & Q a })
             (p : u.1 = v.1)
             (q : rew p in u.2 = v.2)
             (r : rew p in u.3 = v.3)
    : u = v
    := eq_sigT2_uncurried u v (existT2 _ _ p q r).

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_existT2_l {A : Type} {P Q : A -> Type} {u1 : A} {u2 : P u1} {u3 : Q u1} {v : { a : A & P a & Q a }}
             (p : u1 = v.1) (q : rew p in u2 = v.2) (r : rew p in u3 = v.3) : existT2 P Q u1 u2 u3 = v
    := eq_sigT2 (existT2 P Q u1 u2 u3) v p q r.
  Definition eq_existT2_r {A : Type} {P Q : A -> Type} {u : { a : A & P a & Q a }} {v1 : A} {v2 : P v1} {v3 : Q v1}
             (p : u.1 = v1) (q : rew p in u.2 = v2) (r : rew p in u.3 = v3) : u = existT2 P Q v1 v2 v3
    := eq_sigT2 u (existT2 P Q v1 v2 v3) p q r.

  (** Equality of [sigT2] when the second property is an hProp *)
  Definition eq_sigT2_hprop {A P Q} (Q_hprop : forall (x : A) (p q : Q x), p = q)
             (u v : { a : A & P a & Q a })
             (p : u = v :> { a : A & P a })
    : u = v
    := eq_sigT2 u v (projT1_eq p) (projT2_eq p) (Q_hprop _ _ _).

  (** Equivalence of equality of [sigT2] with a [sigT2] of equality *)
  (** We could actually prove an isomorphism here, and not just [<->],
      but for simplicity, we don't. *)
  Definition eq_sigT2_uncurried_iff {A P Q}
             (u v : { a : A & P a & Q a })
    : u = v
      <-> { p : u.1 = v.1 &
            rew p in u.2 = v.2 & rew p in u.3 = v.3}.
  Proof.
    split; [ intro; subst; exists obseq_refl ; reflexivity | apply eq_sigT2_uncurried].
  Defined.

  (** Induction principle for [@eq (sigT2 _ _)] *)
  Definition eq_sigT2_rect {A P Q} {u v : { a : A & P a & Q a }} (R : u = v -> Type)
             (f : forall p q r, R (eq_sigT2 u v p q r))
    : forall p, R p.
  Proof.
    intro p.
    specialize (f (projT1_of_sigT2_eq p) (projT2_of_sigT2_eq p) (projT3_eq p)).
    induction u. induction p; exact f.
  Defined.
  Definition eq_sigT2_rec {A P Q u v} (R : u = v :> { a : A & P a & Q a } -> Set) := eq_sigT2_rect R.
  Definition eq_sigT2_ind {A P Q u v} (R : u = v :> { a : A & P a & Q a } -> Prop) := eq_sigT2_rec R.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_sigT2_rect_existT2_l {A P Q} {u1 u2 u3 v} (R : _ -> Type)
             (f : forall p q r, R (@eq_existT2_l A P Q u1 u2 u3 v p q r))
    : forall p, R p
    := eq_sigT2_rect R f.
  Definition eq_sigT2_rect_existT2_r {A P Q} {u v1 v2 v3} (R : _ -> Type)
             (f : forall p q r, R (@eq_existT2_r A P Q u v1 v2 v3 p q r))
    : forall p, R p
    := eq_sigT2_rect R f.
  Definition eq_sigT2_rect_existT2 {A P Q} {u1 u2 u3 v1 v2 v3} (R : _ -> Type)
             (f : forall p q r, R (@eq_existT2_curried A P Q u1 v1 u2 v2 u3 v3 p q r))
    : forall p, R p
    := eq_sigT2_rect R f.

  (** We want uncurried versions so [inversion_sigma] can accept
      intropatterns, but we use [ex2] types for the induction
      hypothesis to avoid extraction errors about informative
      inductive types having Prop instances *)
  Definition eq_sigT2_rect_uncurried {A P Q} {u v : { a : A & P a & Q a }} (R : u = v -> Type)
             (f : forall pqr : exists2 p : u.1 = v.1, _ & _, R (eq_sigT2 u v (ex_proj1 pqr) (ex_proj2 pqr) (ex_proj3 pqr)))
    : forall p, R p
    := eq_sigT2_rect R (fun p q r => f (ex_intro2 _ _ p q r)).
  Definition eq_sigT2_rec_uncurried {A P Q u v} (R : u = v :> { a : A & P a & Q a } -> Set) := eq_sigT2_rect_uncurried R.
  Definition eq_sigT2_ind_uncurried {A P Q u v} (R : u = v :> { a : A & P a & Q a } -> Prop) := eq_sigT2_rec_uncurried R.

  (** Equivalence of equality of [sigT2] involving hProps with equality of the first components *)
  Definition eq_sigT2_hprop_iff {A P Q} (Q_hprop : forall (x : A) (p q : Q x), p = q)
             (u v : { a : A & P a & Q a })
    : u = v <-> (u = v :> { a : A & P a })
    := conj (fun p => f_equal (@sig_of_sig2 _ _ _) p) (eq_sigT2_hprop Q_hprop u v).

  (** Non-dependent classification of equality of [sigT] *)
  Definition eq_sigT2_nondep {A B C : Type} (u v : { a : A & B & C })
             (p : u.1 = v.1) (q : u.2 = v.2) (r : u.3 = v.3)
    : u = v
    := @eq_sigT2 _ _ _ u v p (eq_trans (rew_const _ _) q) (eq_trans (rew_const _ _) r).

  (** Classification of transporting across an equality of [sigT2]s *)
  Lemma rew_sigT2 {A x} {P : A -> Type} (Q R : forall a, P a -> SProp)
        (u : { p : P x | Q x p & R x p })
        {y} (H : x = y)
    : rew [fun a => { p : P a | Q a p & R a p }] H in u
      = existT2
          (Q y)
          (R y)
          (rew H in u.1)
          (srew dependent [(fun x H => Q x (rew H in u.1))] H in (proj2_SProp_sig u))
          (srew dependent [(fun x H => R x (rew H in u.1))] H in (proj3_SProp_sig u)).
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sigT2.
Global Arguments eq_existT2_curried A P Q _ _ _ _ _ _ !p !q !r / .

(** Equality for [sig2] *)
Section sig2.
  (* We make [sig_of_sig2] a coercion so we can use [proj1], [proj2] on [sig2] *)
  Local Coercion sig_of_sig2 : sig2P >-> sigP.
  Local Coercion ex_of_ex2 : ex2 >-> ex.
  Local Unset Implicit Arguments.
  (** Projecting an equality of a pair to equality of the first components *)
  Definition sig_of_sig2_eq {A} {P Q : A -> SProp} {u v : { a : A | P a & Q a }} (p : u = v)
    : u = v :> { a : A | P a }
    := f_equal _ p.
  Definition proj1_sig_of_sig2_eq {A} {P Q : A -> SProp} {u v : { a : A | P a & Q a }} (p : u = v)
    : proj1_sig u = proj1_sig v
    := proj1_sig_eq (sig_of_sig2_eq p).

  (** Equality of [sig2] is itself a [sig2] (backwards-reasoning version) *)
  Definition eq_sig2_uncurried {A} {P Q : A -> SProp} (u v : { a : A | P a & Q a })
             (pqr : proj1_sig u = proj1_sig v)
    : u = v.
  Proof.
    destruct u as [u1 u2 u3], v as [v1 v2 v3]; simpl in *.
    destruct pqr; reflexivity.
  Qed.

  Lemma eq_exist2_curried {A : Type} {P Q : A -> SProp} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1}
             (p : u1 = v1) : exist2 P Q u1 u2 u3 = exist2 P Q v1 v2 v3.
  Proof.
    apply eq_sig2_uncurried; exact p.
  Qed.

  (** Curried version of proving equality of sigma types *)
  Definition eq_sig2 {A} {P Q : A -> SProp} (u v : { a : A | P a & Q a })
             (p : proj1_sig u = proj1_sig v)
    : u = v
    := eq_sig2_uncurried u v p.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_exist2_l {A : Type} {P Q : A -> SProp} {u1 : A} {u2 : P u1} {u3 : Q u1} {v : { a : A | P a & Q a }}
             (p : u1 = proj1_sig v) : exist2 P Q u1 u2 u3 = v
    := eq_sig2 (exist2 P Q u1 u2 u3) v p.
  Definition eq_exist2_r {A : Type} {P Q : A -> SProp} {u : { a : A | P a & Q a }} {v1 : A} {v2 : P v1} {v3 : Q v1}
             (p : proj1_sig u = v1) : u = exist2 P Q v1 v2 v3
    := eq_sig2 u (exist2 P Q v1 v2 v3) p.

  (** Equality of [sig2] when the second property is an hProp *)
  Definition eq_sig2_hprop {A} {P Q : A -> SProp}
             (u v : { a : A | P a & Q a })
             (p : u = v :> { a : A | P a })
    : u = v
    := eq_sig2 u v (proj1_sig_eq p).

  (** Induction principle for [@eq (sig2 _ _)] *)
  Definition eq_sig2_rect {A P Q} {u v : { a : A | P a & Q a }} (R : u = v -> Type)
             (f : forall p, R (eq_sig2 u v p))
    : forall p, R p.
  Proof.
    intro p.
    exact (f (proj1_sig_of_sig2_eq p)).
  Defined.
  Definition eq_sig2_rec {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Set) := eq_sig2_rect R.
  Definition eq_sig2_ind {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Prop) := eq_sig2_rec R.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_sig2_rect_exist2_l {A P Q} {u1 u2 u3 v} (R : _ -> Type)
             (f : forall p, R (@eq_exist2_l A P Q u1 u2 u3 v p))
    : forall p, R p
    := eq_sig2_rect R f.
  Definition eq_sig2_rect_exist2_r {A P Q} {u v1 v2 v3} (R : _ -> Type)
             (f : forall p, R (@eq_exist2_r A P Q u v1 v2 v3 p))
    : forall p, R p
    := eq_sig2_rect R f.
  Definition eq_sig2_rect_exist2 {A P Q} {u1 u2 u3 v1 v2 v3} (R : _ -> Type)
             (f : forall p, R (@eq_exist2_curried A P Q u1 v1 u2 v2 u3 v3 p))
    : forall p, R p
    := eq_sig2_rect R f.

  (** We want uncurried versions so [inversion_sigma] can accept
      intropatterns, but we use [ex2] types for the induction
      hypothesis to avoid extraction errors about informative
      inductive types having Prop instances *)
  Definition eq_sig2_rect_uncurried {A P Q} {u v : { a : A | P a & Q a }} (R : u = v -> Type)
             (f : forall pqr : proj1_sig u = proj1_sig v, R (eq_sig2 u v pqr))
    : forall p, R p
    := eq_sig2_rect R f.
  Definition eq_sig2_rec_uncurried {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Set) := eq_sig2_rect_uncurried R.
  Definition eq_sig2_ind_uncurried {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Prop) := eq_sig2_rec_uncurried R.

  (** Equivalence of equality of [sig2] involving hProps with equality of the first components *)
  Definition eq_sig2_hprop_iff {A} {P Q : A -> SProp}
             (u v : { a : A | P a & Q a })
    : u = v <-> (u = v :> { a : A | P a })
    := conj (fun p => f_equal (@sig_of_sig2 _ _ _) p) (eq_sig2_hprop u v).

  (** Non-dependent classification of equality of [sig] *)
  Definition eq_sig2_nondep {A} {B C : SProp} (u v : @sig2 A (fun _ => B) (fun _ => C))
             (p : proj1_sig u = proj1_sig v)
    : u = v
    := @eq_sig2 _ _ _ u v p.

  (** Classification of transporting across an equality of [sig2]s *)
  Notation rew_sig2 := rew_sigT2.

End sig2.

(** [sumbool] is a boolean type equipped with the justification of
    their value *)

Inductive sumbool (A B:SProp) : Set :=
  | left : A -> {A} + {B}
  | right : B -> {A} + {B}
 where "{ A } + { B }" := (sumbool A B) : type_scope.

Add Printing If sumbool.

Arguments left {A B} _, [A] B _.
Arguments right {A B} _ , A [B] _.

Register sumbool as core.sumbool.type.

(** [sumor] is an option type equipped with the justification of why
    it may not be a regular value *)

Inductive sumor (A:Type) (B:Prop) : Type :=
  | inleft : A -> A + {B}
  | inright : B -> A + {B}
 where "A + { B }" := (sumor A B) : type_scope.

Add Printing If sumor.

Arguments inleft {A B} _ , [A] B _.
Arguments inright {A B} _ , A [B] _.

(* Unset Universe Polymorphism. *)

(** Various forms of the axiom of choice for specifications *)

Section Choice_lemmas.

  Variables S S' : Set.
  Variable R : S -> S' -> SProp.
  Variable R' : S -> S' -> Set.
  Variables R1 R2 : S -> SProp.

  Lemma Choice :
   (forall x:S, {y:S' | R x y}) -> {f:S -> S' | forall z:S, R z (f z)}.
  Proof.
   intro H.
   exists (fun z => proj1_sig (H z)).
   intro z; destruct (H z); assumption.
  Defined.

  Lemma Choice2 :
   (forall x:S, {y:S' & R' x y}) -> {f:S -> S' & forall z:S, R' z (f z)}.
  Proof.
    intro H.
    exists (fun z => projT1 (H z)).
    intro z. induction (H z) using sigT_rect; assumption.
  Defined.

  Lemma bool_choice :
   (forall x:S, {R1 x} + {R2 x}) ->
     {f:S -> bool | forall x:S, f x = true /\ R1 x \/ f x = false /\ R2 x}.
  Proof.
    intro H.
    exists (fun z:S => if H z then true else false).
    intro z; destruct (H z); auto.
  Defined.

End Choice_lemmas.

Section Dependent_choice_lemmas.

  Variable X : Type.
  Variable R : X -> X -> SProp.

  Lemma dependent_choice :
    (forall x:X, {y | R x y}) ->
    forall x0, {f : nat -> X | f O = x0 /\ forall n, R (f n) (f (S n))}.
  Proof.
    intros H x0.
    set (f:=fix f n := match n with O => x0 | S n' => proj1_sig (H (f n')) end).
    exists f.
    split.
    - reflexivity.
    - intro n; induction n; simpl; apply proj2_SProp_sig.
  Defined.

End Dependent_choice_lemmas.


 (** A result of type [(Exc A)] is either a normal value of type [A] or
     an [error] :

     [Inductive Exc [A:Type] : Type := value : A->(Exc A) | error : (Exc A)].

     It is implemented using the option type. *)
Section Exc.
  Variable A : Type.

  Definition Exc := option A.
  Definition value := @Some A.
  Definition error := @None A.
End Exc.
Arguments error {A}.

Definition except := False_rec. (* for compatibility with previous versions *)

Arguments except [P] _.

Theorem absurd_set : forall (A:SProp) (C:Set), A -> ~ A -> C.
Proof.
  intros A C h1 h2.
  apply SFalse_rec.
  apply (h2 h1).
Defined.

#[global]
Hint Resolve left right inleft inright: core.
#[global]
Hint Resolve exist exist2 existT existT2: core.
