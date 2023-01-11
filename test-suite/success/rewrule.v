Inductive rewrite@{i} {A : Type@{i}} (a: A) (b: A) := rewrite_intro.
Notation "a ==> b" := (rewrite_intro a b) (at level 80).
Notation "[ x .. y ] |- t" :=
  (fun x => .. (fun y => t) ..)
  (at level 200, x binder, only parsing).

Symbol pplus : nat -> nat -> nat.
Notation "a ++ b" := (pplus a b).

Definition addn0 := [n] |- n ++ 0 ==> n.
Definition addnS := [n n'] |- n ++ S n' ==> S (n ++ n').
Definition add0n := [n] |- 0 ++ n ==> n.
Definition addSn := [n n'] |- S n ++ n' ==> S (n ++ n').

Rewrite Rule addn0.
Rewrite Rule addnS.
Rewrite Rule add0n.
Rewrite Rule addSn.

Check eq_refl : 5 ++ 10 = 15.
Check (fun _ _ => eq_refl) : forall n n', 2 + n ++ 3 + n' = 5 + (n ++ n').
Check (fun _ _ _ => eq_refl) : forall n n' n'', 2 + n ++ 1 + n' ++ 2 + n'' = 5 + (n ++ n' ++ n'').

Symbol raise : forall P: Type, P.

Definition raise_bool := [P p p'] |-
  match raise bool as b return P b with
    true => p | false => p'
  end ==> raise (P (raise bool)).

Rewrite Rule raise_bool.

Check eq_refl : match raise bool as b return true = b with true => eq_refl | false => raise _ end = raise (true = raise bool).

Check eq_refl : match raise bool as b return b = b with true | false => eq_refl end = raise (raise bool = raise bool).

Symbol brk : bool -> bool -> bool.
Definition brk1 := [b] |- brk true b ==> true.
Definition brk2 := [b] |- brk b true ==> false.
Rewrite Rule brk1.
Rewrite Rule brk2.

Lemma f0 : False.
  cut { b | brk true b = brk b true}.
  2: exists true; reflexivity.
  intros [b H].
  cbn in H.
  discriminate.
Qed.


Definition f b (H : brk true b = brk b true) : False :=
  eq_ind true (fun e => if e then True else False) I false H.

Eval lazy in (f true eq_refl). (* = I : False *)


Universe u.
Symbol id@{i} : Type@{i} -> Type@{u}.

Definition idrew := [t: Type] |- id t ==> t.
Rewrite Rule idrew.


Definition U : Type@{u} := id Type@{u}.
Check U : U.

Definition id'@{i} : Type@{i} -> Type@{u} := fun (t: Type@{i}) => t.
Fail Definition U' : Type@{u} := id' Type@{u}.

Require Import Coq.Logic.Hurkens.
Definition f' : False := TypeNeqSmallType.paradox U eq_refl.
