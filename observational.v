Require Import Logic. 

Rewrite Rule cast_refl.
Rewrite Rule cast_pi.

(** Observational Coq setup  *)

Set Universe Polymorphism.

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
| vnil : n ~ 0 -> vect A n
| vcons : forall (a : A) (m : nat) (v : vect A m), n ~ S m -> vect A n.

(* equalities for vectors *)
Check (obseq_vnil_0:forall (A B : Type) (n m : nat), vect A n ~ vect B m -> (n ~ 0) ~ (m ~ 0)).
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
