import Mathlib

/-!
# A352356: Number of ways to write 12*n + 5 as 2*x^2 + 5*y^2 + 9*z^2 + x*y*z, where x, y and z are nonnegative integers.

Source: https://oeis.org/A352356
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; verified for n = 0..10^6): for each n = 0, 1, 2, ... we
can write 12*n + 5 as 2*x^2 + 5*y^2 + 9*z^2 + x*y*z with x, y, z nonnegative integers. (The entry's
further remark "it seems that a(n) = 1 only for n = 0, 2, 5, 12, 65, 86, 155, 338, 21030" is not
stated here.)

Formalization notes:
* Controls (computed): 12n + 5 has such a representation for every n < 3000.
-/

namespace OMA.S_oeis_a352356



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, ∃ x y z : ℕ, 2 * x ^ 2 + 5 * y ^ 2 + 9 * z ^ 2 + x * y * z = 12 * n + 5 := by
  sorry

end OMA.S_oeis_a352356
