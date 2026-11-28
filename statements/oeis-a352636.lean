import Mathlib

/-!
# A352636: Number of ways to write n as a^2 + 3*b^2 + c^4 + 2*d^4 + a*b*c*d, where a,b,c,d are nonnegative integers.

Source: https://oeis.org/A352636
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 except for n = 46. (The further remark on
the values with a(n) = 1 is not stated here.)

Formalization notes:
* "a(n) > 0 except for n = 46" (a(46) = 0) is stated as: n is represented iff n ≠ 46.
* Controls (computed): among n < 6000 only n = 46 is not represented.
-/

namespace OMA.S_oeis_a352636



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, (∃ a b c d : ℕ, a ^ 2 + 3 * b ^ 2 + c ^ 4 + 2 * d ^ 4 + a * b * c * d = n) ↔ n ≠ 46 := by
  sorry

end OMA.S_oeis_a352636
