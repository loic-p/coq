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
  
  