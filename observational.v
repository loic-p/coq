(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Require Import Logic.

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
  Eval lazy in (cast (A -> C) (A -> C) obseq_refl f).

End Basic_Test.

(** Tests for inductive types *)
Set Universe Polymorphism.
Set Observational Inductives.

Inductive vect (A : Type) : nat -> Type :=
| vnil : vect A 0
| vcons : forall (a : A) (n : nat) (v : vect A n), vect A (S n).

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
