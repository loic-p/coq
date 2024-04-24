(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Set Universe Polymorphism.

(* The observational equality *)

Inductive obseq@{u} (A : Type@{u}) (a : A) : forall (b : A), SProp :=
| obseq_refl : obseq A a a.
Notation "a ~ b" := (obseq _ a b) (at level 50).
Arguments obseq {A} a _.
Arguments obseq_refl {A a} , [A] a.

Definition obseq_trans {A : Type} {a b c : A} (e : a ~ b) (e' : b ~ c) : a ~ c :=
  obseq_sind _ b (fun X _ => a ~ X) e c e'.
Notation "e @@@ f" := (obseq_trans e f) (at level 40, left associativity, only parsing).

Definition obseq_sym {A : Type} {a b : A} (e : a ~ b) : b ~ a :=
  obseq_sind _ a (fun X _ => X ~ a) obseq_refl b e.

(* Type casting *)

Symbol cast@{u} : forall (A B : Type@{u}), @obseq@{u+1} Type@{u} A B -> A -> B.
Notation "e # a" := (cast _ _ e a) (at level 55, only parsing).

(* SProp casting *)
(* We do not want to use sort polymorphism for cast, to avoid useless (and potentially looping)
   computations in SProp *)

Definition cast_prop (A B : SProp) (e : @obseq@{Set+1} SProp A B) (a : A) := obseq_sind SProp A (fun X _ => X) a B e.
Notation "e #% a" := (cast_prop _ _ e a) (at level 40, only parsing).

Rewrite Rule cast_refl :=
| cast ?A ?A _ ?t >-> ?t.

(* We can use cast to derive large elimination principles for obseq *)

Definition ap {A B} (f : A -> B) {x y} (e : x ~ y) : f x ~ f y :=
  obseq_sind _ x (fun y _ => f x ~ f y) obseq_refl _ e.

Definition apd {A} {a} (P : forall b : A, a ~ b -> Type) (b : A) (e : a ~ b) : (P a obseq_refl) ~ (P b e) :=
  obseq_sind _ a (fun b e => (P a obseq_refl) ~ (P b e)) obseq_refl b e.

Definition obseq_rect@{u v} : forall (A : Type@{u}) (a : A) (P : forall b : A, obseq@{u} a b -> Type@{v}),
    P a obseq_refl@{u} -> forall (b : A) (e : obseq@{u} a b), P b e :=
  fun A a P t b e => cast@{v} (P a obseq_refl) (P b e) (apd P b e) t.

Definition obseq_rec@{u} : forall (A : Type@{u}) (a : A) (P : forall b : A, obseq@{u} a b -> Set),
    P a obseq_refl@{u} -> forall (b : A) (e : obseq@{u} a b), P b e :=
  fun A a P t b e => cast@{Set} (P a obseq_refl) (P b e) (apd P b e) t.

(* The Prop eliminator is an axiom.
   The observational equality should not be used with Prop anyway. *)
Axiom obseq_ind@{u} : forall (A : Type@{u}) (a : A) (P : forall b : A, obseq@{u} a b -> Prop),
    P a obseq_refl@{u} -> forall (b : A) (e : obseq@{u} a b), P b e.

(** Definition of the observational equality on pi's *)

Parameter obseq_forall_1@{u v} : forall {A A' : Type@{u}} {B : A -> Type@{v}} {B' : A' -> Type@{v}},
    @obseq@{max(u+1,v+1)} Type@{max(u,v)} (forall (x : A), B x) (forall (x : A'), B' x) -> @obseq@{u+1} Type@{u} A' A.

Parameter obseq_forall_2@{u v} : forall {A A' : Type@{u}} {B : A -> Type@{v}} {B' : A' -> Type@{v}}
                                        (e : @obseq@{max(u+1,v+1)} Type@{max(u,v)} (forall (x : A), B x) (forall (x : A'), B' x)),
  forall (x : A'), @obseq@{v+1} Type@{v} (B (obseq_forall_1@{u v} e # x)) (B' x).

Parameter funext : forall {A B} (f g : forall (x : A), B x), (forall (x : A), f x ~ g x) -> f ~ g.

Rewrite Rule cast_pi :=
| @{u?} |- cast@{u} (forall (x : ?A), ?B) (forall (x : ?A'), ?B') ?e ?f
   >-> fun (x : ?A') => cast ?B@{x := cast ?A' ?A (obseq_forall_1 ?e) x}
                             ?B'@{x := x}
                             (obseq_forall_2@{u u} ?e x)
                             (?f (cast ?A' ?A (obseq_forall_1 ?e) x)).

(** Definition of the observational equality on strict propositions *)

Parameter propext : forall {A B : SProp}, (A -> B) -> (B -> A) -> A ~ B.

(** Lemmas that describe equalities between telescopes.
    Those are needed in the Fording translation to avoid the use of a heterogeneous equality.
    Here we only prove them up to ap_ty5, meaning that we can handle 4 indices at most. *)

Definition ap_ty1 (A : Type) (B : A -> Type)
  (a0 : A) (a1 : A) (ae : a0 ~ a1)
  : (B a0) ~ (B a1).
Proof.
  exact (obseq_sind A a0 (fun x _ => (B a0) ~ (B x)) obseq_refl a1 ae).
Qed.

Definition ap_ty2 (A : Type) (B : A -> Type) (C : forall (a : A) (b : B a), Type)
  (a0 : A) (a1 : A) (ae : a0 ~ a1)
  (b0 : B a0) (b1 : B a1) (be : cast (B a0) (B a1) (ap_ty1 A B a0 a1 ae) b0 ~ b1)
  : (C a0 b0) ~ (C a1 b1).
Proof.
  exact (obseq_sind A a0
           (fun x e => forall (y : B x) (ye : cast (B a0) (B x) (ap_ty1 A B a0 x e) b0 ~ y)
              , (C a0 b0) ~ (C x y))
           (fun y ye => ap_ty1 (B a0) (C a0) b0 y ye)
           a1 ae b1 be).
Qed.

Definition ap_ty3 (A : Type) (B : A -> Type) (C : forall (a : A) (b : B a), Type) (D : forall (a : A) (b : B a) (c : C a b), Type)
  (a0 : A) (a1 : A) (ae : a0 ~ a1)
  (b0 : B a0) (b1 : B a1) (be : cast (B a0) (B a1) (ap_ty1 A B a0 a1 ae) b0 ~ b1)
  (c0 : C a0 b0) (c1 : C a1 b1) (ce : cast (C a0 b0) (C a1 b1) (ap_ty2 A B C a0 a1 ae b0 b1 be) c0 ~ c1)
  : (D a0 b0 c0) ~ (D a1 b1 c1).
Proof.
  exact (obseq_sind A a0
           (fun x e => forall (y : B x) (ye : cast (B a0) (B x) (ap_ty1 A B a0 x e) b0 ~ y)
                              (z : C x y) (ze : cast (C a0 b0) (C x y) (ap_ty2 A B C a0 x e b0 y ye) c0 ~ z)
              , (D a0 b0 c0) ~ (D x y z))
           (fun y ye z ze => ap_ty2 (B a0) (C a0) (D a0) b0 y ye c0 z ze)
           a1 ae b1 be c1 ce).
Qed.

Definition ap_ty4 (A : Type) (B : A -> Type) (C : forall (a : A) (b : B a), Type) (D : forall (a : A) (b : B a) (c : C a b), Type) (E : forall (a : A) (b : B a) (c : C a b) (d : D a b c), Type)
  (a0 : A) (a1 : A) (ae : a0 ~ a1)
  (b0 : B a0) (b1 : B a1) (be : cast (B a0) (B a1) (ap_ty1 A B a0 a1 ae) b0 ~ b1)
  (c0 : C a0 b0) (c1 : C a1 b1) (ce : cast (C a0 b0) (C a1 b1) (ap_ty2 A B C a0 a1 ae b0 b1 be) c0 ~ c1)
  (d0 : D a0 b0 c0) (d1 : D a1 b1 c1) (de : cast (D a0 b0 c0) (D a1 b1 c1) (ap_ty3 A B C D a0 a1 ae b0 b1 be c0 c1 ce) d0 ~ d1)
  : (E a0 b0 c0 d0) ~ (E a1 b1 c1 d1).
Proof.
  exact (obseq_sind A a0
           (fun x e => forall (y : B x) (ye : cast (B a0) (B x) (ap_ty1 A B a0 x e) b0 ~ y)
                              (z : C x y) (ze : cast (C a0 b0) (C x y) (ap_ty2 A B C a0 x e b0 y ye) c0 ~ z)
                              (t : D x y z) (te : cast (D a0 b0 c0) (D x y z) (ap_ty3 A B C D a0 x e b0 y ye c0 z ze) d0 ~ t)
              , (E a0 b0 c0 d0) ~ (E x y z t))
           (fun y ye z ze t te => ap_ty3 (B a0) (C a0) (D a0) (E a0) b0 y ye c0 z ze d0 t te)
           a1 ae b1 be c1 ce d1 de).
Qed.

Definition ap_ty5 (A : Type) (B : A -> Type) (C : forall (a : A) (b : B a), Type) (D : forall (a : A) (b : B a) (c : C a b), Type)
  (E : forall (a : A) (b : B a) (c : C a b) (d : D a b c), Type)
  (F : forall (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d), Type)
  (a0 : A) (a1 : A) (ae : a0 ~ a1)
  (b0 : B a0) (b1 : B a1) (be : cast (B a0) (B a1) (ap_ty1 A B a0 a1 ae) b0 ~ b1)
  (c0 : C a0 b0) (c1 : C a1 b1) (ce : cast (C a0 b0) (C a1 b1) (ap_ty2 A B C a0 a1 ae b0 b1 be) c0 ~ c1)
  (d0 : D a0 b0 c0) (d1 : D a1 b1 c1) (de : cast (D a0 b0 c0) (D a1 b1 c1) (ap_ty3 A B C D a0 a1 ae b0 b1 be c0 c1 ce) d0 ~ d1)
  (e0 : E a0 b0 c0 d0) (e1 : E a1 b1 c1 d1) (ee : cast (E a0 b0 c0 d0) (E a1 b1 c1 d1) (ap_ty4 A B C D E a0 a1 ae b0 b1 be c0 c1 ce d0 d1 de) e0 ~ e1)
  : (F a0 b0 c0 d0 e0) ~ (F a1 b1 c1 d1 e1).
Proof.
  exact (obseq_sind A a0
           (fun x e => forall (y : B x) (ye : cast (B a0) (B x) (ap_ty1 A B a0 x e) b0 ~ y)
                              (z : C x y) (ze : cast (C a0 b0) (C x y) (ap_ty2 A B C a0 x e b0 y ye) c0 ~ z)
                              (t : D x y z) (te : cast (D a0 b0 c0) (D x y z) (ap_ty3 A B C D a0 x e b0 y ye c0 z ze) d0 ~ t)
                              (u : E x y z t) (ue : cast (E a0 b0 c0 d0) (E x y z t) (ap_ty4 A B C D E a0 x e b0 y ye c0 z ze d0 t te) e0 ~ u)
              , (F a0 b0 c0 d0 e0) ~ (F x y z t u))
           (fun y ye z ze t te u ue => ap_ty4 (B a0) (C a0) (D a0) (E a0) (F a0) b0 y ye c0 z ze d0 t te e0 u ue)
           a1 ae b1 be c1 ce d1 de e1 ee).
Qed.


(** Tests cast for functions *)

Section Basic_Test.
  Variable A B C : Set.
  Variable obseq_fun1 : (A -> C) ~ (B -> C).
  Variable obseq_fun2 : (C -> A) ~ (C -> B).
  Variable f : A -> C.
  Variable g : C -> A.

  (* remark that when the domain/codomain match, one of the casts is eliminated *)
  Eval lazy in (cast (A -> C) (B -> C) (obseq_fun1) f).
  Eval lazy in (cast (C -> A) (C -> B) (obseq_fun2) g).
  Eval lazy in (cast (A -> C) (A -> C) obseq_refl f).

End Basic_Test.

(** Tests for inductive types *)
Set Universe Polymorphism.
Set Observational Inductives.

Inductive vect (A : Type) : nat -> Type :=
| vnil : vect A 0
| vcons : forall (a : A) (n : nat) (v : vect A n), vect A (S n).

Monomorphic Universe u.
Parameter A : Set.
Parameter absurd : vect nat 2 ~ vect A 3.

Fixpoint vect_length (A : Type) (n : nat) (v : vect A n) : nat :=
  match v with
  | vnil _ => 0
  | vcons _ _ m w => 1 + vect_length A m w
  end.

Definition vect1 : vect nat 2 := vcons nat 2 1 (vcons nat 3 0 (vnil nat)).
Definition vect2 : vect A 3 := cast (vect nat 2) (vect A 3) absurd vect1.
Eval cbn in (vect_length A 3 vect2). (* equals 2! *)
