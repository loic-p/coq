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

Definition sig_rect@{s s' s''| u u' u''|} :
  forall [A : Type@{s|u}] [P : A -> Type@{s'|u'}]
    (P0 : sig P -> Type@{s''|u''}),
    (forall (x : A) (p : P x), P0 (exist P x p)) -> forall s : sig P, P0 s :=
  fun A P P0 f s =>
    match s as s0 return (P0 s0) with
          | exist _ x p => f x p
    end.

Register sig as core.sig.type.
Register exist as core.sig.intro.
Register sig_rect as core.sig.rect.

Definition sig2_rect@{s s' s''| u u' v' u''|} :
  forall [A : Type@{s|u}] [P : A -> Type@{s'|u'}]
    [Q : A -> Type@{s'|v'}]
    (P0 : sig2 P Q -> Type@{s''|u''}),
    (forall (x : A) (p : P x) (q : Q x), P0 (exist2 P Q x p q)) ->
    forall s : sig2 P Q, P0 s :=
  fun A P Q P0 f s =>
    match s as s0 return (P0 s0) with
          | exist2 _ _ x y p => f x y p
    end.

(* Notations *)

Arguments sig (A P)%_type.
Arguments sig2 (A P Q)%_type.

Notation "{ x & P }" := (sig (fun x => P)) : type_scope.
Notation "{ x & P & Q }" := (sig2 (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A & P }" := (sig (A:=A) (fun x => P)) : type_scope.
Notation "{ x : A & P & Q }" := (sig2 (A:=A) (fun x => P) (fun x => Q)) :
  type_scope.

Notation "{ ' pat & P }" := (sig (fun pat => P)) : type_scope.
Notation "{ ' pat & P & Q }" := (sig2 (fun pat => P) (fun pat => Q)) : type_scope.
Notation "{ ' pat : A & P }" := (sig (A:=A) (fun pat => P)) : type_scope.
Notation "{ ' pat : A & P & Q }" := (sig2 (A:=A) (fun pat => P) (fun pat => Q)) :
  type_scope.

Add Printing Let sig.
Add Printing Let sig2.

(** Projections of [sig]

    An element [y] of a subset [{x:A | (P x)}] is the pair of an [a]
    of type [A] and of a proof [h] that [a] satisfies [P].  Then
    [(proj1_sig y)] is the witness [a] and [(proj2_sig y)] is the
    proof of [(P a)] *)

Definition proj1_sig@{s s'|u v| } (A:Type@{s|u}) (P:A -> Type@{s'|v})
     (e:sig@{_ _ s|_ _} P) := match e with
                                    | exist _ a b => a
                                    end.

Definition proj2_sig@{s|u v| } (A:Type@{s|u}) (P:A -> Type@{s|v})
    (e:sig P) :=
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
  (X : sig2@{s s' s''|u v v'} P Q) : sig@{s s' s''|u v} P :=
  match X with exist2 _ _ a p q => exist P a p end.

Definition proj3_sig@{s|u v v' v''|u <= v'', v <= v''} (A:Type@{s|u})
    (P:A -> Type@{s|v}) (Q:A -> Type@{s|v'})
    (e:sig2 P Q) :=
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

  Definition proj3_SProp_sig (e : sig2@{Type SProp Type |_ _ _} P Q) :=
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


(** [sig2] of a predicate on [Prop]s can be turned into [ex2] *)

Definition ex2_of_sig2 (A : Type) (P Q : A -> Prop) (X : sig2 P Q) : ex2 P Q
  := ex_intro2 P Q (proj1_sig (sig_of_sig2 X)) (proj2_sig (sig_of_sig2 X)) (proj3_sig X).

(** [sigT2] of a predicate on [Prop]s can be turned into [ex2] *)

Definition ex2_of_sigT2 (A : Type) (P Q : A -> Prop) (X : sigT2 P Q) : ex2 P Q
  := ex2_of_sig2 (sig2_of_sigT2 X).

(** η Principles *)
Definition sigT_eta {A P} (p : { a : A & P a })
  : p = existT _ (projT1 p) (projT2 p).
Proof. destruct p; reflexivity. Defined.

Definition sig_eta {A P} (p : { a : A | P a })
  : p = exist _ (proj1_sig p) (proj2_sig p).
Proof. destruct p; reflexivity. Defined.

Definition sigT2_eta {A P Q} (p : { a : A & P a & Q a })
  : p = existT2 _ _ (projT1 (sigT_of_sigT2 p)) (projT2 (sigT_of_sigT2 p)) (projT3 p).
Proof. destruct p; reflexivity. Defined.

Definition sig2_eta {A P Q} (p : { a : A | P a & Q a })
  : p = exist2 _ _ (proj1_sig (sig_of_sig2 p)) (proj2_sig (sig_of_sig2 p)) (proj3_sig p).
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
  Definition projT1_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
    : u.1 = v.1
    := f_equal (fun x => x.1) p.

  (** Projecting an equality of a pair to equality of the second components *)
  Definition projT2_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
    : rew projT1_eq p in u.2 = v.2
    := rew dependent p in eq_refl.

  (** Equality of [sigT] is itself a [sigT] (forwards-reasoning version) *)
  Definition eq_existT_uncurried {A : Type} {P : A -> Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : { p : u1 = v1 & rew p in u2 = v2 })
    : (u1; u2) = (v1; v2).
  Proof.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  (** Equality of [sigT] is itself a [sigT] (backwards-reasoning version) *)
  Definition eq_sigT_uncurried {A : Type} {P : A -> Type} (u v : { a : A & P a })
             (pq : { p : u.1 = v.1 & rew p in u.2 = v.2 })
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

  Local Notation "(= u ; v )" := (eq_existT_curried u v) (at level 0, format "(= u ;  '/  ' v )").

  Lemma eq_existT_curried_map {A A' P P'} (f:A -> A') (g:forall u:A, P u -> P' (f u))
    {u1 v1 : A} {u2 : P u1} {v2 : P v1} (p : u1 = v1) (q : rew p in u2 = v2) :
    f_equal (fun x => (f x.1; g x.1 x.2)) (= p; q) =
    (= f_equal f p; f_equal_dep2 f g p q).
  Proof.
    destruct p, q. reflexivity.
  Defined.

  Lemma eq_existT_curried_trans {A P} {u1 v1 w1 : A} {u2 : P u1} {v2 : P v1} {w2 : P w1}
    (p : u1 = v1) (q : rew p in u2 = v2)
    (p' : v1 = w1) (q': rew p' in v2 = w2) :
    eq_trans (= p; q) (= p'; q') =
      (= eq_trans p p'; eq_trans_map p p' q q').
  Proof.
    destruct p', q'. reflexivity.
  Defined.

  Theorem eq_existT_curried_congr {A P} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
    {p p' : u1 = v1} {q : rew p in u2 = v2} {q': rew p' in u2 = v2}
    (r : p = p') : rew [fun H => rew H in u2 = v2] r in q = q' -> (= p; q) = (= p'; q').
  Proof.
    destruct r, 1. reflexivity.
  Qed.

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
    split; [ intro; subst; exists eq_refl; reflexivity | apply eq_sigT_uncurried ].
  Defined.

  (** Induction principle for [@eq (sigT _)] *)
  Definition eq_sigT_rect {A P} {u v : { a : A & P a }} (Q : u = v -> Type)
             (f : forall p q, Q (eq_sigT u v p q))
    : forall p, Q p.
  Proof. intro p; specialize (f (projT1_eq p) (projT2_eq p)); destruct u, p; exact f. Defined.
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
  Lemma rew_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : { p : P x & Q x p }) {y} (H : x = y)
    : rew [fun a => { p : P a & Q a p }] H in u
      = existT
          (Q y)
          (rew H in u.1)
          (rew dependent H in (u.2)).
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
  Definition proj1_sig_eq {A} {P : A -> Prop} {u v : { a : A | P a }} (p : u = v)
    : proj1_sig u = proj1_sig v
    := f_equal (@proj1_sig _ _) p.

  (** Projecting an equality of a pair to equality of the second components *)
  Definition proj2_sig_eq {A} {P : A -> Prop} {u v : { a : A | P a }} (p : u = v)
    : rew proj1_sig_eq p in proj2_sig u = proj2_sig v
    := rew dependent p in eq_refl.

  (** Equality of [sig] is itself a [sig] (forwards-reasoning version) *)
  Definition eq_exist_uncurried {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : { p : u1 = v1 | rew p in u2 = v2 })
    : exist _ u1 u2 = exist _ v1 v2.
  Proof.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  (** Equality of [sig] is itself a [sig] (backwards-reasoning version) *)
  Definition eq_sig_uncurried {A : Type} {P : A -> Prop} (u v : { a : A | P a })
             (pq : { p : proj1_sig u = proj1_sig v | rew p in proj2_sig u = proj2_sig v })
    : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    apply eq_exist_uncurried; exact pq.
  Defined.

  Lemma eq_exist_curried {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (p : u1 = v1) (q : rew p in u2 = v2) : exist P u1 u2 = exist P v1 v2.
  Proof.
    apply eq_sig_uncurried; exists p; exact q.
  Defined.

  (** Curried version of proving equality of sigma types *)
  Definition eq_sig {A : Type} {P : A -> Prop} (u v : { a : A | P a })
             (p : proj1_sig u = proj1_sig v) (q : rew p in proj2_sig u = proj2_sig v)
    : u = v
    := eq_sig_uncurried u v (exist _ p q).

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_exist_l {A : Type} {P : A -> Prop} {u1 : A} {u2 : P u1} {v : { a : A | P a }}
             (p : u1 = proj1_sig v) (q : rew p in u2 = proj2_sig v) : exist _ u1 u2 = v
    := eq_sig (exist _ u1 u2) v p q.
  Definition eq_exist_r {A : Type} {P : A -> Prop} {u : { a : A | P a }} {v1 : A} {v2 : P v1}
             (p : proj1_sig u = v1) (q : rew p in proj2_sig u = v2) : u = exist _ v1 v2
    := eq_sig u (exist _ v1 v2) p q.

  (** Induction principle for [@eq (sig _)] *)
  Definition eq_sig_rect {A P} {u v : { a : A | P a }} (Q : u = v -> Type)
             (f : forall p q, Q (eq_sig u v p q))
    : forall p, Q p.
  Proof. intro p; specialize (f (proj1_sig_eq p) (proj2_sig_eq p)); destruct u, p; exact f. Defined.
  Definition eq_sig_rec {A P u v} (Q : u = v :> { a : A | P a } -> Set) := eq_sig_rect Q.
  Definition eq_sig_ind {A P u v} (Q : u = v :> { a : A | P a } -> Prop) := eq_sig_rec Q.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_sig_rect_exist_l {A P} {u1 u2 v} (Q : _ -> Type)
             (f : forall p q, Q (@eq_exist_l A P u1 u2 v p q))
    : forall p, Q p
    := eq_sig_rect Q f.
  Definition eq_sig_rect_exist_r {A P} {u v1 v2} (Q : _ -> Type)
             (f : forall p q, Q (@eq_exist_r A P u v1 v2 p q))
    : forall p, Q p
    := eq_sig_rect Q f.
  Definition eq_sig_rect_exist {A P} {u1 u2 v1 v2} (Q : _ -> Type)
             (f : forall p q, Q (@eq_exist_curried A P u1 v1 u2 v2 p q))
    : forall p, Q p
    := eq_sig_rect Q f.

  (** We want uncurried versions so [inversion_sigma] can accept
      intropatterns, but we use [ex] types for the induction
      hypothesis to avoid extraction errors about informative
      inductive types having Prop instances *)
  Definition eq_sig_rect_uncurried {A P} {u v : { a : A | P a }} (Q : u = v -> Type)
             (f : forall pq : exists p : proj1_sig u = proj1_sig v, _, Q (eq_sig u v (ex_proj1 pq) (ex_proj2 pq)))
    : forall p, Q p
    := eq_sig_rect Q (fun p q => f (ex_intro _ p q)).
  Definition eq_sig_rec_uncurried {A P u v} (Q : u = v :> { a : A | P a } -> Set) := eq_sig_rect_uncurried Q.
  Definition eq_sig_ind_uncurried {A P u v} (Q : u = v :> { a : A | P a } -> Prop) := eq_sig_rec_uncurried Q.

  (** Equality of [sig] when the property is an hProp *)
  Definition eq_sig_hprop {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : { a : A | P a })
             (p : proj1_sig u = proj1_sig v)
    : u = v
    := eq_sig u v p (P_hprop _ _ _).

  (** Equivalence of equality of [sig] with a [sig] of equality *)
  (** We could actually prove an isomorphism here, and not just [<->],
      but for simplicity, we don't. *)
  Definition eq_sig_uncurried_iff {A} {P : A -> Prop}
             (u v : { a : A | P a })
    : u = v <-> { p : proj1_sig u = proj1_sig v | rew p in proj2_sig u = proj2_sig v }.
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply eq_sig_uncurried ].
  Defined.

  (** Equivalence of equality of [sig] involving hProps with equality of the first components *)
  Definition eq_sig_hprop_iff {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : { a : A | P a })
    : u = v <-> (proj1_sig u = proj1_sig v)
    := conj (fun p => f_equal (@proj1_sig _ _) p) (eq_sig_hprop P_hprop u v).

  Lemma rew_sig {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : { p : P x | Q x p }) {y} (H : x = y)
    : rew [fun a => { p : P a | Q a p }] H in u
      = exist
          (Q y)
          (rew H in proj1_sig u)
          (rew dependent H in proj2_sig u).
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sig.
Global Arguments eq_exist_curried A P _ _ _ _ !p !q / .

(** Equality for [sigT2] *)
Section sigT2.
  (* We make [sigT_of_sigT2] a coercion so we can use [projT1], [projT2] on [sigT2] *)
  Local Coercion sigT_of_sigT2 : sigT2 >-> sigT.
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
    : rew projT1_of_sigT2_eq p in u.2 = v.2
    := rew dependent p in eq_refl.

  (** Projecting an equality of a pair to equality of the third components *)
  Definition projT3_eq {A} {P Q : A -> Type} {u v : { a : A & P a & Q a }} (p : u = v)
    : rew projT1_of_sigT2_eq p in u.3 = v.3
    := rew dependent p in eq_refl.

  (** Equality of [sigT2] is itself a [sigT2] (forwards-reasoning version) *)
  Definition eq_existT2_uncurried {A : Type} {P Q : A -> Type}
             {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1}
             (pqr : { p : u1 = v1
                    & rew p in u2 = v2 & rew p in u3 = v3 })
    : existT2 _ _ u1 u2 u3 = existT2 _ _ v1 v2 v3.
  Proof.
    destruct pqr as [p q r].
    destruct r, q, p; simpl.
    reflexivity.
  Defined.

  (** Equality of [sigT2] is itself a [sigT2] (backwards-reasoning version) *)
  Definition eq_sigT2_uncurried {A : Type} {P Q : A -> Type} (u v : { a : A & P a & Q a })
             (pqr : { p : u.1 = v.1
                    & rew p in u.2 = v.2 & rew p in u.3 = v.3 })
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
      <-> { p : u.1 = v.1
          & rew p in u.2 = v.2 & rew p in u.3 = v.3 }.
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply eq_sigT2_uncurried ].
  Defined.

  (** Induction principle for [@eq (sigT2 _ _)] *)
  Definition eq_sigT2_rect {A P Q} {u v : { a : A & P a & Q a }} (R : u = v -> Type)
             (f : forall p q r, R (eq_sigT2 u v p q r))
    : forall p, R p.
  Proof.
    intro p.
    specialize (f (projT1_of_sigT2_eq p) (projT2_of_sigT2_eq p) (projT3_eq p)).
    destruct u, p; exact f.
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
    := conj (fun p => f_equal (@sigT_of_sigT2 _ _ _) p) (eq_sigT2_hprop Q_hprop u v).

  (** Non-dependent classification of equality of [sigT] *)
  Definition eq_sigT2_nondep {A B C : Type} (u v : { a : A & B & C })
             (p : u.1 = v.1) (q : u.2 = v.2) (r : u.3 = v.3)
    : u = v
    := @eq_sigT2 _ _ _ u v p (eq_trans (rew_const _ _) q) (eq_trans (rew_const _ _) r).

  (** Classification of transporting across an equality of [sigT2]s *)
  Lemma rew_sigT2 {A x} {P : A -> Type} (Q R : forall a, P a -> Prop)
        (u : { p : P x & Q x p & R x p })
        {y} (H : x = y)
    : rew [fun a => { p : P a & Q a p & R a p }] H in u
      = existT2
          (Q y)
          (R y)
          (rew H in u.1)
          (rew dependent H in u.2)
          (rew dependent H in u.3).
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sigT2.
Global Arguments eq_existT2_curried A P Q _ _ _ _ _ _ !p !q !r / .

(** Equality for [sig2] *)
Section sig2.
  (* We make [sig_of_sig2] a coercion so we can use [proj1], [proj2] on [sig2] *)
  Local Coercion sig_of_sig2 : sig2 >-> sig.
  Local Coercion ex_of_ex2 : ex2 >-> ex.
  Local Unset Implicit Arguments.
  (** Projecting an equality of a pair to equality of the first components *)
  Definition sig_of_sig2_eq {A} {P Q : A -> Prop} {u v : { a : A | P a & Q a }} (p : u = v)
    : u = v :> { a : A | P a }
    := f_equal _ p.
  Definition proj1_sig_of_sig2_eq {A} {P Q : A -> Prop} {u v : { a : A | P a & Q a }} (p : u = v)
    : proj1_sig u = proj1_sig v
    := proj1_sig_eq (sig_of_sig2_eq p).

  (** Projecting an equality of a pair to equality of the second components *)
  Definition proj2_sig_of_sig2_eq {A} {P Q : A -> Prop} {u v : { a : A | P a & Q a }} (p : u = v)
    : rew proj1_sig_of_sig2_eq p in proj2_sig u = proj2_sig v
    := rew dependent p in eq_refl.

  (** Projecting an equality of a pair to equality of the third components *)
  Definition proj3_sig_eq {A} {P Q : A -> Prop} {u v : { a : A | P a & Q a }} (p : u = v)
    : rew proj1_sig_of_sig2_eq p in proj3_sig u = proj3_sig v
    := rew dependent p in eq_refl.

  (** Equality of [sig2] is itself a [sig2] (fowards-reasoning version) *)
  Definition eq_exist2_uncurried {A} {P Q : A -> Prop}
             {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1}
             (pqr : { p : u1 = v1
                    | rew p in u2 = v2 & rew p in u3 = v3 })
    : exist2 _ _ u1 u2 u3 = exist2 _ _ v1 v2 v3.
  Proof.
    destruct pqr as [p q r].
    destruct r, q, p; simpl.
    reflexivity.
  Defined.

  (** Equality of [sig2] is itself a [sig2] (backwards-reasoning version) *)
  Definition eq_sig2_uncurried {A} {P Q : A -> Prop} (u v : { a : A | P a & Q a })
             (pqr : { p : proj1_sig u = proj1_sig v
                    | rew p in proj2_sig u = proj2_sig v & rew p in proj3_sig u = proj3_sig v })
    : u = v.
  Proof.
    destruct u as [u1 u2 u3], v as [v1 v2 v3]; simpl in *.
    apply eq_exist2_uncurried; exact pqr.
  Defined.

  Lemma eq_exist2_curried {A : Type} {P Q : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1}
             (p : u1 = v1) (q : rew p in u2 = v2) (r : rew p in u3 = v3) : exist2 P Q u1 u2 u3 = exist2 P Q v1 v2 v3.
  Proof.
    apply eq_sig2_uncurried; exists p; exact q + exact r.
  Defined.

  (** Curried version of proving equality of sigma types *)
  Definition eq_sig2 {A} {P Q : A -> Prop} (u v : { a : A | P a & Q a })
             (p : proj1_sig u = proj1_sig v)
             (q : rew p in proj2_sig u = proj2_sig v)
             (r : rew p in proj3_sig u = proj3_sig v)
    : u = v
    := eq_sig2_uncurried u v (exist2 _ _ p q r).

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_exist2_l {A : Type} {P Q : A -> Prop} {u1 : A} {u2 : P u1} {u3 : Q u1} {v : { a : A | P a & Q a }}
             (p : u1 = proj1_sig v) (q : rew p in u2 = proj2_sig v) (r : rew p in u3 = proj3_sig v) : exist2 P Q u1 u2 u3 = v
    := eq_sig2 (exist2 P Q u1 u2 u3) v p q r.
  Definition eq_exist2_r {A : Type} {P Q : A -> Prop} {u : { a : A | P a & Q a }} {v1 : A} {v2 : P v1} {v3 : Q v1}
             (p : proj1_sig u = v1) (q : rew p in proj2_sig u = v2) (r : rew p in proj3_sig u = v3) : u = exist2 P Q v1 v2 v3
    := eq_sig2 u (exist2 P Q v1 v2 v3) p q r.

  (** Equality of [sig2] when the second property is an hProp *)
  Definition eq_sig2_hprop {A} {P Q : A -> Prop} (Q_hprop : forall (x : A) (p q : Q x), p = q)
             (u v : { a : A | P a & Q a })
             (p : u = v :> { a : A | P a })
    : u = v
    := eq_sig2 u v (proj1_sig_eq p) (proj2_sig_eq p) (Q_hprop _ _ _).

  (** Equivalence of equality of [sig2] with a [sig2] of equality *)
  (** We could actually prove an isomorphism here, and not just [<->],
      but for simplicity, we don't. *)
  Definition eq_sig2_uncurried_iff {A P Q}
             (u v : { a : A | P a & Q a })
    : u = v
      <-> { p : proj1_sig u = proj1_sig v
          | rew p in proj2_sig u = proj2_sig v & rew p in proj3_sig u = proj3_sig v }.
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply eq_sig2_uncurried ].
  Defined.

  (** Induction principle for [@eq (sig2 _ _)] *)
  Definition eq_sig2_rect {A P Q} {u v : { a : A | P a & Q a }} (R : u = v -> Type)
             (f : forall p q r, R (eq_sig2 u v p q r))
    : forall p, R p.
  Proof.
    intro p.
    specialize (f (proj1_sig_of_sig2_eq p) (proj2_sig_of_sig2_eq p) (proj3_sig_eq p)).
    destruct u, p; exact f.
  Defined.
  Definition eq_sig2_rec {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Set) := eq_sig2_rect R.
  Definition eq_sig2_ind {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Prop) := eq_sig2_rec R.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_sig2_rect_exist2_l {A P Q} {u1 u2 u3 v} (R : _ -> Type)
             (f : forall p q r, R (@eq_exist2_l A P Q u1 u2 u3 v p q r))
    : forall p, R p
    := eq_sig2_rect R f.
  Definition eq_sig2_rect_exist2_r {A P Q} {u v1 v2 v3} (R : _ -> Type)
             (f : forall p q r, R (@eq_exist2_r A P Q u v1 v2 v3 p q r))
    : forall p, R p
    := eq_sig2_rect R f.
  Definition eq_sig2_rect_exist2 {A P Q} {u1 u2 u3 v1 v2 v3} (R : _ -> Type)
             (f : forall p q r, R (@eq_exist2_curried A P Q u1 v1 u2 v2 u3 v3 p q r))
    : forall p, R p
    := eq_sig2_rect R f.

  (** We want uncurried versions so [inversion_sigma] can accept
      intropatterns, but we use [ex2] types for the induction
      hypothesis to avoid extraction errors about informative
      inductive types having Prop instances *)
  Definition eq_sig2_rect_uncurried {A P Q} {u v : { a : A | P a & Q a }} (R : u = v -> Type)
             (f : forall pqr : exists2 p : proj1_sig u = proj1_sig v, _ & _, R (eq_sig2 u v (ex_proj1 pqr) (ex_proj2 pqr) (ex_proj3 pqr)))
    : forall p, R p
    := eq_sig2_rect R (fun p q r => f (ex_intro2 _ _ p q r)).
  Definition eq_sig2_rec_uncurried {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Set) := eq_sig2_rect_uncurried R.
  Definition eq_sig2_ind_uncurried {A P Q u v} (R : u = v :> { a : A | P a & Q a } -> Prop) := eq_sig2_rec_uncurried R.

  (** Equivalence of equality of [sig2] involving hProps with equality of the first components *)
  Definition eq_sig2_hprop_iff {A} {P Q : A -> Prop} (Q_hprop : forall (x : A) (p q : Q x), p = q)
             (u v : { a : A | P a & Q a })
    : u = v <-> (u = v :> { a : A | P a })
    := conj (fun p => f_equal (@sig_of_sig2 _ _ _) p) (eq_sig2_hprop Q_hprop u v).

  (** Non-dependent classification of equality of [sig] *)
  Definition eq_sig2_nondep {A} {B C : Prop} (u v : @sig2 A (fun _ => B) (fun _ => C))
             (p : proj1_sig u = proj1_sig v) (q : proj2_sig u = proj2_sig v) (r : proj3_sig u = proj3_sig v)
    : u = v
    := @eq_sig2 _ _ _ u v p (eq_trans (rew_const _ _) q) (eq_trans (rew_const _ _) r).

  (** Classification of transporting across an equality of [sig2]s *)
  Lemma rew_sig2 {A x} {P : A -> Type} (Q R : forall a, P a -> Prop)
        (u : { p : P x | Q x p & R x p })
        {y} (H : x = y)
    : rew [fun a => { p : P a | Q a p & R a p }] H in u
      = exist2
          (Q y)
          (R y)
          (rew H in proj1_sig u)
          (rew dependent H in proj2_sig u)
          (rew dependent H in proj3_sig u).
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sig2.
Global Arguments eq_exist2_curried A P Q _ _ _ _ _ _ !p !q !r / .


(** [sumbool] is a boolean type equipped with the justification of
    their value *)

Inductive sumbool (A B:Prop) : Set :=
  | left : A -> {A} + {B}
  | right : B -> {A} + {B}
 where "{ A } + { B }" := (sumbool A B) : type_scope.

Add Printing If sumbool.

Arguments left {A B} _, [A] B _.
Arguments right {A B} _ , A [B] _.

Register sumbool as core.sumbool.type.

(** [sumor] is an option type equipped with the justification of why
    it may not be a regular value *)

#[universes(template)]
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
  Variable R : S -> S' -> Prop.
  Variable R' : S -> S' -> Set.
  Variables R1 R2 : S -> Prop.

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
    intro z; destruct (H z); assumption.
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
  Variable R : X -> X -> Prop.

  Lemma dependent_choice :
    (forall x:X, {y | R x y}) ->
    forall x0, {f : nat -> X | f O = x0 /\ forall n, R (f n) (f (S n))}.
  Proof.
    intros H x0.
    set (f:=fix f n := match n with O => x0 | S n' => proj1_sig (H (f n')) end).
    exists f.
    split.
    - reflexivity.
    - intro n; induction n; simpl; apply proj2_sig.
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

Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C.
Proof.
  intros A C h1 h2.
  apply False_rec.
  apply (h2 h1).
Defined.

#[global]
Hint Resolve left right inleft inright: core.
#[global]
Hint Resolve exist exist2 existT existT2: core.
