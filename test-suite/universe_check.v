Set Universe Polymorphism.
(* So that by default we only get Set <= a constraints, not Set < a *)

Section test_loop.
  Universes a b c d.
  Constraint b < a.
  Constraint c <= d.
  Fail Constraint d < c.
End test_loop.

Section funext.
  Universes a b c d.

  Constraint Set < a.
  Constraint b < a.
  Constraint Set < c.
  Constraint c < b.
  Constraint d <= a.

  Check Constraint d <= a.
End funext.

Section test_loop.
  Universes a b.
  Constraint a < b.
  Fail Check Constraint b < a.
  Fail Constraint b < a.
End test_loop.

Section test.
Universes a b c d.

Constraint a < b.
Constraint b < c.
Constraint c < d.

Check Constraint Set < b.

End test.

Section test2.
  Universes a b.
  Constraint a <= b.
  Fail Check Constraint a = b.

  Constraint b <= a.
  Check Constraint a = b.
End test2.

Section test3.
  Universes a b c d.
  Constraint a <= c.
  Constraint b <= c.
  Fail Check Constraint a <= b.
  Check Constraint a <= c.
  Constraint a <= d, d <= b.
  Check Constraint a <= b.

  Constraint b <= a.
  Check Constraint a = b, a = d.
End test3.

Set Debug "loop-checking".
Set Debug "loop-checking-global".

Section incr.
  Universe a b c.

  Constraint a <= b + 1.
  Constraint b + 1 <= a.
  Check Constraint b <= a.

  Check Constraint a + 2 = b + 3.

End incr.

Section maximpl.
  Universe a b c.

  Constraint a <= max (b, c).
  Fail Check Constraint a <= b.
  Fail Check Constraint a <= c.
  Check Constraint a <= max (b, c).

  (* If we add this constraint, then max (b, c) = c and a <= c holds *)
  Constraint b <= c.
  Fail Check Constraint a <= b.
  Check Constraint a <= c.

  Check Constraint max (b, c) = c.

End maximpl.

Section merge_noincr.
  Universe a b c.

  Constraint a <= b.
  Constraint b <= c. (* implies b + 2 <= c + 1, so a <= c + 1 *)

  Constraint c <= a. (* Now c + 1 <= a <= c + 1 *)
  Check Constraint c = a.
End merge_noincr.

Section merge_incr.
  Universe a b c.

  Constraint a <= b + 1.
  Constraint b + 1 <= c. (* implies b + 2 <= c + 1, so a <= c + 1 *)

  Constraint c <= a.
  (* Now c = a = b + 1 *)
  Check Constraint c = a, c = b + 1.
End merge_incr.


Section merge_incr_trans.
  Universe a b c.

  Constraint a <= b + 1.
  Constraint b + 1 <= c + 2. (* implies b + 2 <= c + 1, so a <= c + 1 *)

  Fail Constraint c + 3 <= a.
  Constraint c + 2 <= a.
  (* Now c = a = b + 1 *)
  Check Constraint c + 2 = a, c + 1 = b. (* as c + 2 = b + 1, c + 1 = b *)

End merge_incr_trans.

Section merge_incr_all_incr.
  Universe a b c.

  Constraint a + 2 <= b + 1.
  Constraint b + 1 <= c + 6. (* implies b + 2 <= c + 1, so a <= c + 1 *)

  (* Constraint c + 3 <= a + 2.   *)
  Constraint c + 6 <= a + 2.
  (* Now c = a = b + 1 *)
  Check Constraint c + 6 = a + 2, c + 5 = b. (* as c + 2 = b + 1, c + 1 = b *)

End merge_incr_all_incr.
