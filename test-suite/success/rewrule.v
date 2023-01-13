
Axiom symb : nat.
Axiom symb_0 : symb = 0.

Fail Rewrite Rule symb.

Rewrite Rule symb_0.

Definition symb' := Eval lazy in symb.
Check eq_refl : symb' = 0.

Check eq_refl : id symb = 0.

(* bug: unfold_ref_with_args returns None from Rules *)
Fail Check eq_refl : symb = 0.
