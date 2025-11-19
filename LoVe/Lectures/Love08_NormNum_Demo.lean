/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/

import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Util.Qq
import Mathlib.Algebra.Ring.Int.Defs

/-!

This time we'll build up a *normalization* tactic for numeric expressions
whose type is a Semiring. That is, we want to be able to reduce expressions like
`(2 + 3) * 4 + 5` to `25`, where the numerals are interpreted in an arbitrary
type in which numbers are well behaved.

We'll do this first as a `conv` mode tactic. This mode lets us soom in on
subexpressions and rewrite them. One way to prove an equality between numeric
expressions is to normalize each side to a numeral and then try reflexivity.

Here are some examples which `norm_num` should solve.  Solve them by hand, writing out what we want
the tactic to do. Since we plan to write a conv-tactic, you should modify the LHS only:

**write everything inside a `conv_lhs =>` block.**


Useful lemmas: -/
#check Nat.cast_zero
#check Nat.cast_one
#check Nat.cast_two -- etc
#check Nat.cast_add
#check Nat.cast_mul

section
variable {A : Type*} [Semiring A] (x : A)

/-! Exercises: -/

example : (0:A) = ↑(nat_lit 0) := by
  sorry

example : (1:A) = nat_lit 1 := by
  -- dropping the `↑` from now on, since Lean will infer it (look at the infoview here)
  sorry

example : (3:A) = nat_lit 3 := by
  sorry

example : (1:A) + 0 = nat_lit 1 := by
  sorry

example : (1:A) + 3 = nat_lit 4 := by
  sorry

example : (1:A) + 2 + 3 = nat_lit 6 := by
  sorry

example : (1:A) * 2 = nat_lit 2 := by
  sorry

example : (3:A) + 7 = nat_lit 10 := by
  conv_lhs =>
    rewrite [← Nat.cast_ofNat (n := nat_lit 3),
             ← Nat.cast_ofNat (n := nat_lit 7),
             ← Nat.cast_add,
             (rfl : 3 + 7 = 10)]

example : (2:A) * 5 = nat_lit 10 := by
  sorry

example : (2:A) * 5 + 1 = nat_lit 11 := by
  sorry

example : (2:A) * 3 * 5 = nat_lit 30 := by
  sorry

end
