(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Prelude.

Require Import Logic.

Section Relation_Definition.

  Variable A : Type.

  Definition relation := A -> A -> SProp.

  Variable R : relation.


  Section General_Properties_of_Relations.

    Definition reflexive : SProp := forall x:A, R x x.
    Definition transitive : SProp := forall x y z:A, R x y -> R y z -> R x z.
    Definition symmetric : SProp := forall x y:A, R x y -> R y x.
    Definition antisymmetric : SProp := forall x y:A, R x y -> R y x -> x = y.

    (* for compatibility with Equivalence in  ../PROGRAMS/ALG/  *)
    Definition equiv := reflexive /\ transitive /\ symmetric.

  End General_Properties_of_Relations.



  Section Sets_of_Relations.

    Record preorder : SProp :=
      { preord_refl : reflexive; preord_trans : transitive}.

    Record order : SProp :=
      { ord_refl : reflexive;
	ord_trans : transitive;
	ord_antisym : antisymmetric}.

    Record equivalence : SProp :=
      { equiv_refl : reflexive;
	equiv_trans : transitive;
	equiv_sym : symmetric}.

    Record PER : SProp :=  {per_sym : symmetric; per_trans : transitive}.

  End Sets_of_Relations.


  Section Relations_of_Relations.

    Definition inclusion (R1 R2:relation) : SProp :=
      forall x y:A, R1 x y -> R2 x y.

    Definition same_relation (R1 R2:relation) : SProp :=
      inclusion R1 R2 /\ inclusion R2 R1.

    Definition commut (R1 R2:relation) : SProp :=
      forall x y:A,
	R1 y x -> forall z:A, R2 z y ->  exists2 y' : A, R2 y' x & R1 z y'.

  End Relations_of_Relations.


End Relation_Definition.

#[global]
Hint Unfold reflexive transitive antisymmetric symmetric: sets.

#[global]
Hint Resolve Build_preorder Build_order Build_equivalence Build_PER
  preord_refl preord_trans ord_refl ord_trans ord_antisym equiv_refl
  equiv_trans equiv_sym per_sym per_trans: sets.

#[global]
Hint Unfold inclusion same_relation commut: sets.
