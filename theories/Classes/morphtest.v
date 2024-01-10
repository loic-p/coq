Require Import Setoid Coq.Classes.CRelationClasses Coq.Classes.CMorphisms.
Generalizable Variables A eqA B C D R RA RB RC m f x y.

Import ProperNotations.
Open Scope signatureT_scope.
Lemma flip_arrow@{a ar b br ?} {A : Type@{a}} (R : crelation@{a ar} A) (B : Type@{b}) (R' : crelation@{b br} B)
    `(NA : Normalizes A R (flip R'''), NB : Normalizes B R' (flip R'')) :
  Normalizes (A -> B) (R ==> R') (flip (R''' ==> R'')%signatureT).
Proof.
  unfold Normalizes in *. intros.
  rewrite NA, NB. firstorder.
Qed.

#[global]
Instance PartialOrder_proper_type `(PartialOrder A eqA R) :
  Proper (eqA==>eqA==>iffT) R.
Proof.
intros.
apply proper_sym_arrow_iffT_2. 1-2:typeclasses eauto.
intros x x' Hx y y' Hy Hr.
transitivity x.
- generalize (partial_order_equivalence x x'); compute; intuition.
- transitivity y; auto.
  generalize (partial_order_equivalence y y'); compute; intuition.
Qed.
