(** Observational Coq setup  *)

Set Universe Polymorphism.

Inductive rewrite@{i j} {A : Type@{i}} (a: A) (b: A) : Type@{j} := rewrite_intro.
Notation "a ==> b" := (rewrite_intro a b) (at level 80).
Notation "[ x .. y ] |- t" :=
  (fun x => .. (fun y => t) ..)
  (at level 200, x binder, only parsing).

(* Postulating the observational equality *)

Parameter obseq@{u} : forall (A : Type@{u}) (a b : A), SProp.
Notation "a ~ b" := (obseq _ a b) (at level 50).
Parameter obseq_refl : forall {A : Type} (a : A), a ~ a.
Parameter obseq_transp : forall {A : Type} (P : A -> SProp) (a : A) (t : P a) (b : A) (e : a ~ b), P b.

Definition obseq_J {A : Type} (a : A) (P : forall b : A, a ~ b -> SProp) (t : P a (obseq_refl a)) (b : A) (e : a ~ b) : P b e :=
  obseq_transp (fun X => forall (e : a ~ X), P X e) a (fun _ => t) b e e.

Definition obseq_trans {A : Type} {a b c : A} (e : a ~ b) (e' : b ~ c) : a ~ c :=
  obseq_transp (fun X => a ~ X) b e c e'.
Notation "e ** f" := (obseq_trans e f) (at level 50, left associativity, only parsing).

(* Type casting *)

Symbol cast@{u v} : forall (A B : Type@{u}), obseq@{v} Type@{u} A B -> A -> B.
Notation "e # a" := (cast _ _ e a) (at level 40, only parsing).

Definition cast_prop (A B : SProp) (e : A ~ B) (a : A) := obseq_transp (fun X => X) A a B e.
Notation "e #% a" := (cast_prop _ _ e a) (at level 40, only parsing).

Definition cast_refl := [A t e] |- cast A A e t ==> t.
Rewrite Rule cast_refl.

(** Variables for the observational equality on pi's *)

Parameter seq_forall_1 : forall {A A' B B'}, (forall (x : A), B x) ~ (forall (x : A'), B' x) -> A' ~ A.
Parameter seq_forall_2 : forall {A A' B B'} (e : (forall (x : A), B x) ~ (forall (x : A'), B' x)) (x : A'),
    B (seq_forall_1 e # x) ~ B' x.

Parameter funext : forall {A B} (f g : forall (x : A), B x), forall (x : A), f x ~ g x -> f ~ g.

(*
Definition cast_pi : 
  forall (A : Type) (B : A -> Type) (A' : Type) (B' : A' -> Type)
    (e : (forall (x : A), B x) ~ (forall (x : A'), B' x)) f,
    rewrite (f # e)
                  (fun (x : A') => f (x # (seq_forall_1 e)) # (seq_forall_2 e x))
  := [A B A' B' e f] |- (cast (forall (x : A), B x) (forall (x : A'), B' x) e f)
                          ==> (fun (x : A') => (f (x # (seq_forall_1 e))) # (seq_forall_2 e x)).
*)


Definition cast_pi@{u u' v} (A : Type@{u}) (B : A -> Type@{u}) (A' : Type@{u}) (B' : A' -> Type@{u})
         (e : obseq@{u'} Type@{u} (forall (x : A), B x) (forall (x : A'), B' x)) f :
    rewrite@{u v} (cast@{u u'} (forall (x : A), B x) (forall (x : A'), B' x) e f)
                  (fun (x : A') => cast@{u u'} _ _ (seq_forall_2@{u u u u u u' u u' u'} e x)
                                                   (f (cast@{u u'} A' A (seq_forall_1@{u' u u u u u u'} e) x)))
  := e # f ==> fun (x : A') => seq_forall_2 e x # f (seq_forall_1 e # x).
Rewrite Rule cast_pi.

(** Axioms for the observational equality on strict propositions *)

Parameter propext : forall {A B : SProp}, (A -> B) -> (B -> A) -> A ~ B.

(** Some tests *)


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

(* Declaring an inductive automaticall adds equalities and rewrite rules for cast *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : forall (a : A) (l : list A), list A.

(* The following equality has been defined *)
Print obseq_cons_0.

(* The following rewrite rules have been defined *)
Print rewrite_nil.
Print rewrite_cons.

(* Casting a singleton list *)
Section List_Test. 

  Variable A B C : Set.
  Variable obseq_list : list A ~ list B.
  Variable a : A.
  Eval lazy in (cast (list A) (list B) obseq_list (cons A a (nil A))).

  (* forded vectors *)
End List_Test. 

Inductive vect (A : Type) (n : nat) : Type :=
| vnil : obseq nat n 0 -> vect A n
| vcons : forall (a : A) (m : nat) (v : vect A m), obseq nat n (m + 1) -> vect A n.

(* equalities for vectors *)
Print obseq_vnil_0.
Print obseq_vcons_0.
Print obseq_vcons_1.
Print obseq_vcons_2.
Print obseq_vcons_3.

(* rewrite rules for vectors *)
Print rewrite_vnil.
Print rewrite_vcons.

(* forded Martin-Löf identity type *)
Inductive eq (A : Type) (a : A) (b : A) : Type :=
| refl0 : forall (e : a ~ b), eq A a b.

Print obseq_refl0_0.
Print rewrite_refl0.
