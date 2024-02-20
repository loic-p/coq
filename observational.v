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

(* The equality on the universe is annoying, because it needs a superfluous universe level.
   The other option is to have a second observational equality exclusively for universes: *)
Inductive obseqU@{u} (A : Type@{u}) : Type@{u} -> SProp :=
| obseqU_refl : obseqU A A.

(* Type casting *)
(* cast has two universe parameters because we use obseq instead of obseqU *)

Symbol cast@{u v} : forall (A B : Type@{u}), @obseq@{v} Type@{u} A B -> A -> B.
Notation "e # a" := (cast _ _ e a) (at level 55, only parsing).

(* SProp casting *)
(* We do not want to use sort polymorphism for cast, to avoid useless (and potentially looping)
   computations in SProp *)

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

(* The Prop eliminator is an axiom.
   The observational equality should not be used with Prop anyway. *)
Axiom obseq_ind@{u} : forall (A : Type@{u}) (a : A) (P : forall b : A, obseq@{u} a b -> Prop),
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
  Eval lazy in (cast (A -> C) (A -> C) (obseq_refl _) f).

End Basic_Test.

(** Inductive types *)

Set Observational Inductives.

Arguments cast A B {e} t.

(* Declaring an inductive automaticall adds equalities and rewrite rules for cast *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : forall (a : A) (l : list A), list A.

Arguments nil {A}.
Arguments cons {A} a l.

(* The following equality has been defined *)
Print obseq_cons_1.

(* The following rewrite rules have been defined *)
Print rewrite_nil.
Print rewrite_cons.

(* Casting a singleton list *)
Section List_Test.

  Variable A B C : Set.
  Variable obseq_list : list A ~ list B.
  Variable a : A.

  Eval lazy in obseq_list # cons a nil.
  Eval lazy in obseq_refl # cons a nil.

End List_Test.

(* forded vectors *)

Inductive vect (A : Type) (n : nat) : Type :=
| vnil : n ~ 0 -> vect A n
| vcons : forall (a : A) (m : nat) (v : vect A m), n ~ S m -> vect A n.

Arguments vnil {A n e}.
Arguments vcons {A n} a m v {e}.

Notation vnil' := (vnil (e:= obseq_refl)).
Notation vcons' a n v := (vcons a n v (e := obseq_refl)).

(* equalities for vectors *)
Check (obseq_vnil_0:forall (A B : Type) (n m : nat), vect A n ~ vect B m -> (n ~ 0) ~ (m ~ 0)).
Print obseq_vcons_0.
Print obseq_vcons_1.
Print obseq_vcons_2.
Print obseq_vcons_3.

(* rewrite rules for vectors *)
Print rewrite_vnil.
Print rewrite_vcons.

Section Vector_Test.

  Variable A B C : Set.
  Variable obseq_vect : forall {n m}, n ~ m -> vect A n ~ vect B m.
  Variable a : A.
  Variable n : nat.

  Eval lazy in (obseq_vect obseq_refl # vcons' a 0 vnil').
  Eval lazy in (obseq_refl # vcons' a 0 vnil').

End Vector_Test.


(* forded Martin-Löf identity type *)
Inductive Id (A : Type) (a : A) (b : A) : Type :=
| idrefl : forall (e : a ~ b), Id A a b.

Arguments idrefl {A a b}.

Notation idrefl' := (idrefl obseq_refl).

Print obseq_idrefl_0.
Print rewrite_idrefl.

Lemma functional_extensionality A B (f g : A -> B) :
  (forall x y, Id A x y -> Id B (f x) (g y)) -> Id _ f g.
Proof.
  intro Heq; econstructor.
  eapply funext. intro x. specialize (Heq x x idrefl').
  destruct Heq; eauto.
Qed.
