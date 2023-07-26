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

  Variable A B : Set.
  Variable obseq_list : list A ~ list B.
  Variable a : A.

  Eval lazy in obseq_list # cons a nil.
  Eval lazy in obseq_refl # cons a nil.

End List_Test.

(* forded vectors *)

Unset Observational Inductives.

Inductive vect (A : Type) : nat -> Type :=
| vnil : vect A 0
| vcons : forall (a : A) (m : nat) (v : vect A m), vect A (S m).

(*
Inductive vect (A : Type) (n : nat) : Type :=
| vnil : n ~ 0 -> vect A n
| vcons : forall (a : A) (m : nat) (v : vect A m), n ~ S m -> vect A n.
*)

Arguments vnil {A}.
Arguments vcons {A} a m v.

#[unfold_fix] 
Symbol vnil_obs@{u v | u < v} : forall  (A : Type@{u}) n, n ~ 0 -> vect@{u} A n.

#[unfold_fix]
Symbol vcons_obs@{u v | u < v} : forall (A : Type@{u}) (a : A) (m : nat) (v : vect@{u} A m) n, n ~ S m -> vect@{u} A n.

(*
Notation vnil' := (vnil (e:= obseq_refl)).
Notation vcons' a n v := (vcons a n v (e := obseq_refl)).
*)

(* equalities for vectors *)
Parameter obseq_vnil_0@{u u0 u1 | u0 < u1, Set <= u0, u <= u0} : 
  forall (A A0 : Type@{u}) (n n0 : nat) (_ : @obseq@{u1} Type@{u0} (vect@{u} A n) (vect@{u} A0 n0)),
  obseq@{u1} (n ~ O) (n0 ~ O).

Parameter obseq_vcons_0@{u u0 u1 | u0 < u1, Set <= u0, u <= u0} : 
  forall (A A0 : Type@{u}) (n n0 : nat)
  (_ : @obseq@{u1} Type@{u0} (vect@{u} A n) (vect@{u} A0 n0)),
  @obseq@{u1} Type@{u0} A A0.

Parameter obseq_vcons_1@{u u0 u1 | u0 < u1, Set <= u0, u <= u0} :
  forall (A A0 : Type@{u}) (n n0 : nat)
  (e : @obseq@{u1} Type@{u0} (vect@{u} A n) (vect@{u} A0 n0)) 
  (a : A),
  let a0 : A0 := @cast@{u0 u1} A A0 (obseq_vcons_0@{u u0 u1} A A0 n n0 e) a in
  @obseq@{u1} Type@{u0} nat nat.

Parameter obseq_vcons_2@{u u0 u1 | u0 < u1, Set <= u0, u <= u0} :
 forall (A A0 : Type@{u}) (n n0 : nat)
  (e : @obseq@{u1} Type@{u0} (vect@{u} A n) (vect@{u} A0 n0)) 
  (a : A) (m : nat),
  let a0 : A0 := @cast@{u0 u1} A A0 (obseq_vcons_0@{u u0 u1} A A0 n n0 e) a in
  let m0 : nat :=
  @cast@{u0 u1} nat nat (obseq_vcons_1@{u u0 u1} A A0 n n0 e a) m in
@obseq@{u1} Type@{u0} (vect@{u} A m) (vect@{u} A0 m0).

Parameter obseq_vcons_3@{u u0 u1 | u0 < u1, Set <= u0, u <= u0} :
forall (A A0 : Type@{u}) (n n0 : nat)
  (e : @obseq@{u1} Type@{u0} (vect@{u} A n) (vect@{u} A0 n0)) 
  (a : A) (m : nat) (v : vect@{u} A m),
let a0 : A0 := @cast@{u0 u1} A A0 (obseq_vcons_0@{u u0 u1} A A0 n n0 e) a in
let m0 : nat :=
  @cast@{u0 u1} nat nat (obseq_vcons_1@{u u0 u1} A A0 n n0 e a) m in
let v0 : vect@{u} A0 m0 :=
  @cast@{u0 u1} (vect@{u} A m) (vect@{u} A0 m0)
	(obseq_vcons_2@{u u0 u1} A A0 n n0 e a m) v in
  @obseq@{u1} SProp (@obseq@{Set} nat n (S m)) (@obseq@{Set} nat n0 (S m0)).

(* rewrite rules for vectors *)
Definition rewrite_vnil_eq@{u u0 u1 | u0 < u1, Set <= u0, u <= u0} :=
  fun (A A0 : Type@{u}) (n n0 : nat)
  (e : @obseq@{u1} Type@{u0} (vect@{u} A n) (vect@{u} A0 n0))
  (o : @obseq@{Set} nat n O) =>
@rewrite_intro@{u0 u1} (vect@{u} A0 n0)
  (@cast@{u0 u1} (vect@{u} A n) (vect@{u} A0 n0) e (vnil_obs@{u u1} A n o))
  (let o0 : @obseq@{Set} nat n0 O :=
	 cast_prop@{u1} (@obseq@{Set} nat n O) (@obseq@{Set} nat n0 O)
       (obseq_vnil_0@{u u0 u1} A A0 n n0 e) o in
   vnil_obs@{u u1} A0 n0 o0).

Rewrite Rule rewrite_vnil_eq.

Definition rewrite_vnil@{u u0 u1 | u0 < u1, Set <= u0, u <= u0} :=
  fun (A A0 : Type@{u}) (n0 : nat)
  (e : @obseq@{u1} Type@{u0} (vect@{u} A 0) (vect@{u} A0 n0)) =>
@rewrite_intro@{u0 u1} (vect@{u} A0 n0)
  (@cast@{u0 u1} (vect@{u} A 0) (vect@{u} A0 n0) e vnil@{u})
  (let o0 : @obseq@{Set} nat n0 O :=
	 cast_prop@{u1} (@obseq@{Set} nat 0 O) (@obseq@{Set} nat n0 O)
       (obseq_vnil_0@{u u0 u1} A A0 0 n0 e) obseq_refl in
   vnil_obs@{u u1} A0 n0 o0).

Rewrite Rule rewrite_vnil.

Definition rewrite_vcons_eq@{u u0 u1 | u0 < u1, Set <= u0, u <= u0} :=
fun (A A0 : Type@{u}) (n n0 : nat)
  (e : @obseq@{u1} Type@{u0} (vect@{u} A n) (vect@{u} A0 n0)) 
  (a : A) (m : nat) (v : vect@{u} A m) (o : @obseq@{Set} nat n (S m)) =>
@rewrite_intro@{u0 u1} (vect@{u} A0 n0)
  (@cast@{u0 u1} (vect@{u} A n) (vect@{u} A0 n0) e (vcons_obs@{u u1} A a m v n o))
  (let a0 : A0 := @cast@{u0 u1} A A0 (obseq_vcons_0@{u u0 u1} A A0 n n0 e) a
	 in
   let m0 : nat :=
     @cast@{u0 u1} nat nat (obseq_vcons_1@{u u0 u1} A A0 n n0 e a) m in
   let v0 : vect@{u} A0 m0 :=
     @cast@{u0 u1} (vect@{u} A m) (vect@{u} A0 m0)
       (obseq_vcons_2@{u u0 u1} A A0 n n0 e a m) v in
   let o0 : @obseq@{Set} nat n0 (S m0) :=
     cast_prop@{u1} (@obseq@{Set} nat n (S m)) (@obseq@{Set} nat n0 (S m0))
       (obseq_vcons_3@{u u0 u1} A A0 n n0 e a m v) o in
   vcons_obs@{u u1} A0 a0 m0 v0 n0 o0).

Rewrite Rule rewrite_vcons_eq.

Definition rewrite_vcons@{u u0 u1 | u0 < u1, Set <= u0, u <= u0} :=
fun (A A0 : Type@{u}) (m n0 : nat)
  (e : @obseq@{u1} Type@{u0} (vect@{u} A (S m)) (vect@{u} A0 n0)) 
  (a : A) (v : vect@{u} A m) (n := S m) =>
@rewrite_intro@{u0 u1} (vect@{u} A0 n0)
  (@cast@{u0 u1} (vect@{u} A n) (vect@{u} A0 n0) e (vcons@{u} a m v))
  (let a0 : A0 := @cast@{u0 u1} A A0 (obseq_vcons_0@{u u0 u1} A A0 n n0 e) a
	 in
   let m0 : nat :=
     @cast@{u0 u1} nat nat (obseq_vcons_1@{u u0 u1} A A0 n n0 e a) m in
   let v0 : vect@{u} A0 m0 :=
     @cast@{u0 u1} (vect@{u} A m) (vect@{u} A0 m0)
       (obseq_vcons_2@{u u0 u1} A A0 n n0 e a m) v in
   let o0 : @obseq@{Set} nat n0 (S m0) :=
     cast_prop@{u1} (@obseq@{Set} nat n (S m)) (@obseq@{Set} nat n0 (S m0))
       (obseq_vcons_3@{u u0 u1} A A0 n n0 e a m v) obseq_refl in
   vcons_obs@{u u1} A0 a0 m0 v0 n0 o0).

Rewrite Rule rewrite_vcons.

Definition cast_vnil_refl A e := vnil_obs A 0 e ==> vnil.
Rewrite Rule cast_vnil_refl.

Definition cast_vcons_refl A a m v e := vcons_obs A a m v (S m) e ==> vcons a m v.
Rewrite Rule cast_vcons_refl.

Definition obseq_sym {A : Type} {a b : A} (e : a ~ b) : b ~ a :=
  obseq_transp (fun X => X ~ a) a obseq_refl b e.

Definition sprop_irr (A : SProp) (x y : A) (P : A -> SProp): P x -> P y := fun X => X.

Fail Definition ap2 A (P : forall n, vect A n -> Type) n e : P 0 vnil ~ P n (vnil_obs A n e) :=
  obseq_J 0 (fun n e => P 0 vnil ~ P n (vnil_obs A n (obseq_sym e))) obseq_refl n (obseq_sym e).

(*
Axiom vnil_obs'@{u v | u < v} : forall  (A : Type@{u}) n, n ~ 0 -> vect@{u} A n.

Definition ap2 (A:Type) (P : forall n:nat, vect A n -> Type) 
    n e : P 0 (vnil_obs' A 0 obseq_refl) ~ P n (vnil_obs' A n e).
  eapply (sprop_irr.
  exact (obseq_J 0 (fun n e => P 0 (vnil_obs' A 0 obseq_refl) ~ P n (vnil_obs' A n (obseq_sym e))) obseq_refl n (obseq_sym e)).
Qed.
*)

   
Definition ap2 (I:Type) (B : I -> Type) (P : forall i:I, B i -> Type) 
  i0 (c : forall i, i ~ i0 -> B i)  i e e' : 
  P i0 (c i0 e') ~ P i (c i e).

Parameter ap2@{u u0 v} : 
  forall (A:Type@{u}) (P : forall n:nat, vect@{u} A n -> Type@{u0}) 
    n (e : @obseq@{Set} nat n 0), @obseq@{v} _ (P 0 vnil) (P n (vnil_obs@{u v} A n e)).
 
    (*
eapply (sprop_irr _ (obseq_sym (obseq_sym e)) e).
  exact (obseq_J 0 (fun n e => P 0 vnil ~ P n (vnil_obs A n (obseq_sym e))) obseq_refl n (obseq_sym e)).
Qed.
*)

Arguments cast : clear scopes.

(*
Definition vnil_obs_match := fun (A:Type) (P:forall n, vect A n -> Type)
   (Pvnil : P 0 vnil) (Pvcons : forall a m v, P (S m) (vcons a m v)) n e =>
  match (vnil_obs A n e) as vs in (vect _ n) return P n vs with
  | vnil => Pvnil
  | vcons a m v => Pvcons a m v
  end ==> @cast (P 0 vnil) (P n (vnil_obs A n e)) (ap2 A P n e) Pvnil.
Fail Rewrite Rule vnil_obs_match.
*)

Definition vnil_obs_match@{u u' v u1} := fun (A:Type@{u}) (P:forall n, vect@{u} A n -> Type@{u'})
   (Pvnil : P 0 vnil@{u}) (Pvcons : forall a m v, P (S m) (vcons@{u} a m v)) n e =>
  @rewrite_intro@{u u1} (P n (vnil_obs@{u v} A n e))
   (match (vnil_obs@{u v} A n e) as vs in (vect _ n) return P n vs : Type@{u} with
  | vnil => Pvnil
  | vcons a m v => Pvcons a m v
  end) (@cast@{u' v} (P 0 vnil) (P n (vnil_obs@{u v} A n e)) (ap2@{u u' v} A P n e) Pvnil).

Rewrite Rule vnil_obs_match.


Definition vnil_obs_match'@{u u0 v u1} := fun (A:Type@{u}) (P:forall n, vect@{u} A n -> Type@{u0})
   (Pvnil : P 0 vnil@{u}) (Pvcons : forall a m v, P (S m) (vcons@{u} a m v)) n e =>
  @rewrite_intro@{u0 u1} (P n (vnil_obs@{u v} A n e))
   (match (vnil_obs@{u v} A n e) as vs in (vect _ n) return P n vs : Type@{v} with
  | vnil => Pvnil
  | vcons a m v => Pvcons a m v
  end) (@cast@{u0 v} (P 0 vnil) (P n (vnil_obs@{u v} A n e)) (ap2@{u u0 v} A P n e) Pvnil).

Rewrite Rule vnil_obs_match'.

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

Lemma uip A x y (e e' : Id A x y) : Id _ e e'.
Proof.
  econstructor. destruct e, e'. apply obseq_refl.
Qed.    
  