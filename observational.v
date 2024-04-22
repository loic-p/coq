(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Set Universe Polymorphism.
Set Printing All.

(* The observational equality *)

Inductive obseq@{u} (A : Type@{u}) (a : A) : forall (b : A), SProp :=
| obseq_refl : obseq A a a.
Notation "a ~ b" := (obseq _ a b) (at level 50).
Arguments obseq {A} a _.
Arguments obseq_refl {A a} , [A] a.

Definition obseq_trans {A : Type} {a b c : A} (e : a ~ b) (e' : b ~ c) : a ~ c :=
  obseq_sind _ b (fun X _ => a ~ X) e c e'.
Notation "e @@@ f" := (obseq_trans e f) (at level 40, left associativity, only parsing).

(* Type casting *)
(* cast has two universe parameters because we use obseq instead of obseqU *)

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

Definition ap_ty1 (A : Type) (B : A -> Type)
  (a0 : A) (a1 : A) (ae : a0 ~ a1)
  : (B a0) ~ (B a1) :=
  obseq_sind A a0 (fun x _ => (B a0) ~ (B x)) obseq_refl a1 ae.

Definition ap_ty2 (A : Type) (B : A -> Type) (C : forall (a : A) (b : B a), Type)
  (a0 : A) (a1 : A) (ae : a0 ~ a1)
  (b0 : B a0) (b1 : B a1) (be : cast (B a0) (B a1) (ap_ty1 A B a0 a1 ae) b0 ~ b1)
  : (C a0 b0) ~ (C a1 b1) :=
  obseq_sind A a0 (fun x e => forall (y : B x) (ye : cast (B a0) (B x) (ap_ty1 A B a0 x e) b0 ~ y), (C a0 b0) ~ (C x y))
    (fun y ye => ap_ty1 (B a0) (C a0) b0 y ye)
    a1 ae b1 be.

Definition ap_ty3 (A : Type) (B : A -> Type) (C : forall (a : A) (b : B a), Type) (D : forall (a : A) (b : B a) (c : C a b), Type)
  (a0 : A) (a1 : A) (ae : a0 ~ a1)
  (b0 : B a0) (b1 : B a1) (be : cast (B a0) (B a1) (ap_ty1 A B a0 a1 ae) b0 ~ b1)
  (c0 : C a0 b0) (c1 : C a1 b1) (ce : cast (C a0 b0) (C a1 b1) (ap_ty2 A B C a0 a1 ae b0 b1 be) c0 ~ c1)
  : (D a0 b0 c0) ~ (D a1 b1 c1) :=
  obseq_sind A a0 (fun x e => forall (y : B x) (ye : cast (B a0) (B x) (ap_ty1 A B a0 x e) b0 ~ y) (z : C x y) (ze : cast (C a0 b0) (C x y) (ap_ty2 A B C a0 x e b0 y ye) c0 ~ z), (D a0 b0 c0) ~ (D x y z))
    (fun y ye z ze => ap_ty2 (B a0) (C a0) (D a0) b0 y ye c0 z ze)
    a1 ae b1 be c1 ce.

Definition ap_ty4 (A : Type) (B : A -> Type) (C : forall (a : A) (b : B a), Type) (D : forall (a : A) (b : B a) (c : C a b), Type) (E : forall (a : A) (b : B a) (c : C a b) (d : D a b c), Type)
  (a0 : A) (a1 : A) (ae : a0 ~ a1)
  (b0 : B a0) (b1 : B a1) (be : cast (B a0) (B a1) (ap_ty1 A B a0 a1 ae) b0 ~ b1)
  (c0 : C a0 b0) (c1 : C a1 b1) (ce : cast (C a0 b0) (C a1 b1) (ap_ty2 A B C a0 a1 ae b0 b1 be) c0 ~ c1)
  (d0 : D a0 b0 c0) (d1 : D a1 b1 c1) (de : cast (D a0 b0 c0) (D a1 b1 c1) (ap_ty3 A B C D a0 a1 ae b0 b1 be c0 c1 ce) d0 ~ d1)
  : (E a0 b0 c0 d0) ~ (E a1 b1 c1 d1) :=
  obseq_sind A a0 (fun x e => forall (y : B x) (ye : cast (B a0) (B x) (ap_ty1 A B a0 x e) b0 ~ y) (z : C x y) (ze : cast (C a0 b0) (C x y) (ap_ty2 A B C a0 x e b0 y ye) c0 ~ z) (t : D x y z) (te : cast (D a0 b0 c0) (D x y z) (ap_ty3 A B C D a0 x e b0 y ye c0 z ze) d0 ~ t), (E a0 b0 c0 d0) ~ (E x y z t))
    (fun y ye z ze t te => ap_ty3 (B a0) (C a0) (D a0) (E a0) b0 y ye c0 z ze d0 t te)
    a1 ae b1 be c1 ce d1 de.

(* Set Printing Universes. *)

About ap_ty1.
About ap_ty2.
About ap_ty3.
About ap_ty4.

(** Inductive types *)
Set Universe Polymorphism.
Set Observational Inductives.


Axiom A0 : Type.
Axiom A1 : A0 -> Type.

Axiom X0 : forall (a0 : A0) (a1 : A1 a0), Type.
Axiom X1 : forall (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1), Type.
Axiom X2 : forall (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0), Type.
Axiom X3 : forall (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0) (x2 : X2 a0 a1 x0 x1), Type.

Axiom B0 : forall (a0 : A0) (a1 : A1 a0), Type.
Axiom B1 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1), Type.
Axiom B2 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0), Type.

Axiom t0 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1), X0 a0 a1.
Axiom t1 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1), X1 a0 a1 (t0 a0 a1 b0 b1 b2).
Axiom t2 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1), X2 a0 a1 (t0 a0 a1 b0 b1 b2) (t1 a0 a1 b0 b1 b2).
Axiom t3 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1), X3 a0 a1 (t0 a0 a1 b0 b1 b2) (t1 a0 a1 b0 b1 b2) (t2 a0 a1 b0 b1 b2).

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Inductive V (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0) : Type :=
| cV : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1) (e : @obseq (X0 a0 a1) x0 (t0 a0 a1 b0 b1 b2)), V a0 a1 x0 x1.

Inductive IV (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0) : Type :=
| cIV : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1) (e : @obseq (X0 a0 a1) x0 (t0 a0 a1 b0 b1 b2)),
      @obseq (X1 a0 a1 (t0 a0 a1 b0 b1 b2))
        (cast (X1 a0 a1 x0) (X1 a0 a1 (t0 a0 a1 b0 b1 b2))
           (ap_ty1 (X0 a0 a1) (fun x2 : X0 a0 a1 => X1 a0 a1 x2) x0 (t0 a0 a1 b0 b1 b2) e) x1)
        (t1 a0 a1 b0 b1 b2) -> IV a0 a1 x0 x1.

Inductive III (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0) : Type :=
| cIII : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1) (e : @obseq (X0 a0 a1) x0 (t0 a0 a1 b0 b1 b2)),
    let h : (X1 a0 a1 x0) ~ (X1 a0 a1 (t0 a0 a1 b0 b1 b2)) :=
      ap_ty1 (X0 a0 a1) (fun x2 : X0 a0 a1 => X1 a0 a1 x2) x0
        (t0 a0 a1 b0 b1 b2) e in
    forall
      _ : @obseq (X1 a0 a1 (t0 a0 a1 b0 b1 b2))
            (cast (X1 a0 a1 x0) (X1 a0 a1 (t0 a0 a1 b0 b1 b2)) h x1)
            (t1 a0 a1 b0 b1 b2), III a0 a1 x0 x1.

Inductive II (a0 : A0) (a1 : A1 a0) : forall (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0), Type :=
| cII : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1), II a0 a1 (t0 a0 a1 b0 b1 b2) (t1 a0 a1 b0 b1 b2).

Inductive I (a0 : A0) (a1 : A1 a0) : forall (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0) (x2 : X2 a0 a1 x0 x1) (x3 : X3 a0 a1 x0 x1 x2), Type :=
| c0 : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1), I a0 a1 (t0 a0 a1 b0 b1 b2) (t1 a0 a1 b0 b1 b2) (t2 a0 a1 b0 b1 b2) (t3 a0 a1 b0 b1 b2).

Inductive vect (A : Type) : nat -> Type :=
| vnil : vect A 0
| vcons : forall (a : A) (n : nat) (v : vect A n), vect A (S n).

Rewrite Rule plz :=
| @{u?} |- cast (vect@{u} _ 0) (vect@{u} ?T0 ?n0) ?o (vnil ?T)
 >-> let e : @obseq nat ?n0 O := cast_prop (@obseq nat 0 O) (@obseq nat ?n0 O) (obseq_vnil_0 ?T ?T0 0 ?n0 ?o) (@obseq_refl nat O) in
     vnil_cast ?T0 ?n0 e.

Parameter grille pain : Type.
Parameter toast : vect grille 0 ~ vect pain 1.
Parameter uhh : vect grille 0 ~ vect grille 0.
Parameter yea : 1 ~ 0.
Eval lazy in (cast (vect grille 0) (vect pain 1) toast (vnil_cast grille 0 obseq_refl)).

Definition test : cast (vect grille 0) (vect pain 1) toast (vnil grille) = vnil_cast pain 1 yea := eq_refl.

(* Print II_rect. *)
(* About cII_cast. *)

Parameter a0 : A0.
Parameter a1 : A1 a0.
Parameter y0 : B0 a0 a1.
Parameter y1 : B1 a0 a1 y0.
Parameter y2 : B2 a0 a1 y0 y1.
Parameter z0 : X0 a0 a1.
Parameter z1 : X1 a0 a1 z0.
Parameter P : forall (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0) (_ : II a0 a1 x0 x1), Type.
Parameter f : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1), P (t0 a0 a1 b0 b1 b2) (t1 a0 a1 b0 b1 b2) (cII_cast a0 a1 (t0 a0 a1 b0 b1 b2) (t1 a0 a1 b0 b1 b2) b0 b1 b2 obseq_refl obseq_refl).
Parameter ez0 : @obseq (X0 a0 a1) z0 (t0 a0 a1 y0 y1 y2).
Parameter ez1 : @obseq (X1 a0 a1 (t0 a0 a1 y0 y1 y2)) (cast (X1 a0 a1 z0) (X1 a0 a1 (t0 a0 a1 y0 y1 y2)) (ap_ty1 (X0 a0 a1) (X1 a0 a1) z0 (t0 a0 a1 y0 y1 y2) ez0) z1) (t1 a0 a1 y0 y1 y2).

Definition H0 : @obseq (II a0 a1 (t0 a0 a1 y0 y1 y2) (t1 a0 a1 y0 y1 y2))
                  (cast (II a0 a1 z0 z1) (II a0 a1 (t0 a0 a1 y0 y1 y2) (t1 a0 a1 y0 y1 y2)) (ap_ty2 (X0 a0 a1) (X1 a0 a1) (II a0 a1) z0 (t0 a0 a1 y0 y1 y2) ez0 z1 (t1 a0 a1 y0 y1 y2) ez1) (cII_cast a0 a1 z0 z1 y0 y1 y2 ez0 ez1))
                  ~~~> cII_cast a0 a1 (t0 a0 a1 y0 y1 y2) (t1 a0 a1 y0 y1 y2) y0 y1 y2 osef osef
                  (cII_cast a0 a1 (t0 a0 a1 y0 y1 y2) (t1 a0 a1 y0 y1 y2) y0 y1 y2 obseq_refl obseq_refl).

(* Should hold by refl!!!!!!!! *)

Definition H1 : obseqU (P z0 z1 (cII_cast a0 a1 z0 z1 y0 y1 y2 ez0 ez1))
                       (P (t0 a0 a1 y0 y1 y2) (t1 a0 a1 y0 y1 y2)
                          (cII_cast a0 a1 (t0 a0 a1 y0 y1 y2) (t1 a0 a1 y0 y1 y2) y0 y1 y2 obseq_refl obseq_refl)) :=

  ap_ty3 (X0 a0 a1) (X1 a0 a1) (II a0 a1) P
    z0 (t0 a0 a1 y0 y1 y2) ez0
    z1 (t1 a0 a1 y0 y1 y2) ez1
    (cII_cast a0 a1 z0 z1 y0 y1 y2 ez0 ez1) (cII_cast a0 a1 (t0 a0 a1 y0 y1 y2) (t1 a0 a1 y0 y1 y2) y0 y1 y2 obseq_refl obseq_refl) refl.


match cII_cast a0 a1 z0 z1 y0 y1 y2 (ez0 : x0 ~ (t0 a0 a1 b0 b1 b2)) (ez1 : cast _ _ _ x1 ~ (t1 a0 a1 b0 b1 b2))
      as i0 in (II _ _ x0 x1) return (P x0 x1 i0) with
       | cII _ _ b0 b1 b2 => f b0 b1 b2
end.

==>

cast (P (t0 a0 a1 y0 y1 y2) (t1 a0 a1 y0 y1 y2) (cII_cast a0 a1 (t0 a0 a1 y0 y1 y2) (t1 a0 a1 y0 y1 y2) y0 y1 y2 refl refl))
     (P z0 z1 (cII_cast a0 a1 z0 z1 y0 y1 y2 ez0 ez1))
     H1
     (f y0 y1 y2)

Inductive I (a0 : A0) (a1 : A1 a0) : forall (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0) (x2 : X2 a0 a1 x0 x1) (x3 : X3 a0 a1 x0 x1 x2), Type :=
| c0 : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0) (b2 : B2 a0 a1 b0 b1), I a0 a1 (t0 a0 a1 b0 b1 b2) (t1 a0 a1 b0 b1 b2) (t2 a0 a1 b0 b1 b2) (t3 a0 a1 b0 b1 b2).

Inductive vect (A : Type) : nat -> Type :=
| vnil : vect A 0
| vcons : forall (a : A) (n : nat) (v : vect A n), vect A (S n).

Inductive test@{u v} : forall (x : Type@{u} -> Type@{v}), x nat -> Set :=
| ctest : test (fun _ => nat) 0.

About ctest.
About ctest_cast.

About I.
About c0_cast.
About vnil_cast.
About vcons_cast.


Axiom A0 : Type.
Axiom A1 : A0 -> Type.
Axiom X0 : forall (a0 : A0) (a1 : A1 a0), Type.
Axiom X1 : forall (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1), Type.
Axiom X1p : forall (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1), Type.
Axiom X2 : forall (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (x1p : X1p a0 a1 x0) (x1 : X1 a0 a1 x0), Type.
Axiom B0 : forall (a0 : A0) (a1 : A1 a0), Type.
Axiom B1 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1), Type.
Axiom t0 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0), X0 a0 a1.
Axiom t1 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0), X1p a0 a1 (t0 a0 a1 b0 b1).
Axiom f : forall (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (x1p : X1p a0 a1 x0), X1 a0 a1 x0.
Axiom t2 : forall (a0 : A0) (a1 : A1 a0) (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0), X2 a0 a1 (t0 a0 a1 b0 b1) (t1 a0 a1 b0 b1) (f a0 a1 (t0 a0 a1 b0 b1) (t1 a0 a1 b0 b1)).

(* Inductive I (a0 : A0) (a1 : A1 a0) : forall (x0 : X0 a0 a1) (x1 : X1p a0 a1 x0), Type := *)
(* | c0 : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0), I a0 a1 (t0 a0 a1 b0 b1) (t1 a0 a1 b0 b1). *)

Inductive I (a0 : A0) (a1 : A1 a0) : forall (x0 : X0 a0 a1) (x1p : X1p a0 a1 x0) (x1 := f a0 a1 x0 x1p) (x2 : X2 a0 a1 x0 x1p x1), Type :=
| c0 : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0), I a0 a1 (t0 a0 a1 b0 b1) (t1 a0 a1 b0 b1) (t2 a0 a1 b0 b1).

Set Printing Universes.

Universe Levels u v.
Axiom A : Type@{u}.
Axiom B : Type@{v}.

Axiom f@{w} : Type@{w} -> Type@{w}.

Check (A -> B).


Inductive IF (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (x1p : X1p a0 a1 x0) (x1 := f a0 a1 x0 x1p) (x2 : X2 a0 a1 x0 x1p x1) : Type :=
| c0F : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0)
               (e0 : x0 ~ t0 a0 a1 b0 b1)
               (E1 := ap_ty (X0 a0 a1) (X1p a0 a1) x0 (t0 a0 a1 b0 b1) e0)
               (e1 : cast _ _ E1 x1p ~ t1 a0 a1 b0 b1)
               (E2 := ap_ty2 (X0 a0 a1) (fun x0 => X1p a0 a1 x0) (fun x0 x1p => X2 a0 a1 x0 x1p (f a0 a1 x0 x1p)) x0 (t0 a0 a1 b0 b1) e0 x1p (t1 a0 a1 b0 b1) e1)
               (e2 : cast _ _ E2 x2 ~ t2 a0 a1 b0 b1)
  , IF a0 a1 x0 x1p x2.

Check c0.
Check c0F.

(* let's think for a second here... *)
cast (I a0 a1 (t0 a0 a1 b0 b1) (t1 a0 a1 b0 b1) (t2 a0 a1 b0 b1)) (I a0' a1' x0' x1' x2') e (c0 a0 a1 b0 b1)
==> ...inventing universe levels...

Definition I' := IF.
Definition c0' (a0 : A0) (a1 : A1 a0) : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0), I' a0 a1 (t0 a0 a1 b0 b1) (t1 a0 a1 b0 b1) (t2 a0 a1 b0 b1) :=
  fun b0 b1 => c0F a0 a1 (t0 a0 a1 b0 b1) (t1 a0 a1 b0 b1) (t2 a0 a1 b0 b1) b0 b1 obseq_refl obseq_refl obseq_refl obseq_refl obseq_refl.




match c0F a0 a1 x0' x1' x2' b0' b1' ... : I' a0 a1 x0' x1' x2' return (fun x0 x1 x2 => P[ x0 x1 x2 ]) with
| c0 _ _ b0 b1 => t[ a0 a1 b0 b1 ] : P[ (t0 a0 a1 b0 b1) (t1 a0 a1 b0 b1) (t2 a0 a1 b0 b1) ]
end

  ==>

cast
  P[ (t0 a0 a1 b0' b1') (t1 a0 a1 b0' b1') (t2 a0 a1 b0' b1') ]
  P[ x0' x1' x2' ]
  (heterogeneously: refl P _ _ e0 _ _ e1 _ _ e2) (* homogeneously this is kinda awful :( *)
  t[ a0 a1 b0' b1' ]

(* Option 1: garder deux hypothèses par indice <--- pas vraiment possible, puisqu'il va falloir faire le travail au moment du match
   Option 2: autoriser jusqu'à 10 indices et prouver les trucs correctement
   Option 3: utiliser une égalité hétérogène <--- la bonne manière tbh *)

(* ideal forded inductive type with an equality between telescopes *)
Inductive IF_tel (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (x1 : X1 a0 a1 x0) (x2 : X2 a0 a1 x0 x1) : Type :=
| c0F_tel : forall (b0 : B0 a0 a1) (b1 : B1 a0 a1 b0)
                   (𝐞 : < x0, x1, x2 > ~_{ < X0, X1, X2 > } < t0, t1, t2 >)
  , IF_tel a0 a1 x0 x1 x2.

(* we are already quite decent at telescopes equalities tho! *)
(* but only between inhabitants of the telescope Type, Type, Type... which is simpler tbh *)

< x0, x1, x2, x3 > ~_{ < X0, X1, X2, X3 > } < t0, t1, t2, t3 >

e0 :                                        t0 ~ x0 at X0
e1 :         cast (X1 t0) (X1 x0) (X1 @ e0) t1 ~ x1 at X1 x0
e2 :       cast (X2 t0 t1) (X2 x0 x1) (...) t2 ~ x2 at X2 x0 x1
e3 : cast (X3 t0 t1 t2) (X3 x0 x1 x2) (...) t3 ~ x3 at X3 x0 x1 x2

E0 : X0 ~ X0
e0 : E0 # t0 ~ x0
E1 : X1 t0 ~ X1 x0
e1 : E1 # t1 ~ x1
E2 : X2 t0 t1 ~ X2 x0 x1
e2 : E2 # t2 ~ x2

(* here we realise that we kind of want heteq... *)

Axiom eq_X1 : forall (a0 : A0) (a1 : A1 a0) (x0 : X0 a0 a1) (y0 : X0 a0 a1) (e0 : x0 ~ y0), X1 a0 a1 x0 ~ X1 a0 a1 y0.
Axiom eq_X2 : forall (a0 : A0) (a1 : A1 a0)
                     (x0 : X0 a0 a1) (y0 : X0 a0 a1)
                     (x1 : X1 a0 a1 x0) (y1 : X1 a0 a1 y0)
                     (e0 : x0 ~ y0)
                     (x1' := cast (X1 a0 a1 x0) (X1 a0 a1 y0) (eq_X1 a0 a1 x0 y0 e0) (x1))
                     (e1 : x1' ~ y1), X2 a0 a1 x0 x1 ~ X2 a0 a1 y0 y1.



(* Declaring an inductive automaticall adds equalities and rewrite rules for cast *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : forall (a : A) (l : list A), list A.

(* Casting a singleton list *)
Section List_Test.

  Variable A B C : Set.
  Variable obseq_list : list A ~ list B.
  Variable a : A.

  Eval lazy in obseq_list # cons A a (nil A).
  Eval lazy in obseq_refl # cons A a (nil A).

End List_Test.

(* forded vectors *)

Inductive vect (A : Type) (n : nat) : Type :=
| vnil : n ~ 0 -> vect A n
| vcons : forall (a : A) (m : nat) (v : vect A m), n ~ S m -> vect A n.

Arguments vnil {A n e}.
Arguments vcons {A n} a m v {e}.

About obseq_vnil_0.
About obseq_vcons_0.
About obseq_vcons_1.
About obseq_vcons_2.

Notation vnil' := (vnil (e:= obseq_refl)).
Notation vcons' a n v := (vcons a n v (e := obseq_refl)).

(* equalities for vectors *)
Check (obseq_vnil_0:forall (A B : Type) (n m : nat), vect A n ~ vect B m -> (n ~ 0) ~ (m ~ 0)).
Print obseq_vcons_0.
Print obseq_vcons_1.
Print obseq_vcons_2.
Print obseq_vcons_3.

Section Vector_Test.

  Variable A B C : Set.
  Variable obseq_vect : forall {n m}, n ~ m -> vect A n ~ vect B m.
  Variable a : A.
  Variable n : nat.

  Eval lazy in (obseq_vect obseq_refl # vcons' a 0 vnil').
  Eval lazy in (obseq_refl # vcons' a 0 vnil').

End Vector_Test.


(* forded Martin-Löf identity type *)
Inductive Id (A : Type) (a : A) (b : A) : Set :=
| idrefl : forall (e : a ~ b), Id A a b.

Arguments idrefl {A a b}.

Notation idrefl' := (idrefl obseq_refl).

Print obseq_idrefl_0.

Lemma functional_extensionality A B (f g : A -> B) :
  (forall x y, Id A x y -> Id B (f x) (g y)) -> Id _ f g.
Proof.
  intro Heq; econstructor.
  eapply funext. intro x. specialize (Heq x x idrefl').
  destruct Heq; eauto.
Qed.
