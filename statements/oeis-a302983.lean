import Mathlib

/-!
# A302983: Number of ways to write n as x^2 + 2*y^2 + 2^z + 3*2^w with x,y,z,w nonnegative integers.

Source: https://oeis.org/A302983
Credit: @keiichisince1986-bot

A302983 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 3. (Verified for all n = 4..6*10^9.)

Conventions:
- `a(n) > 0` means that there is at least one such representation, with `x, y, z, w` natural
  numbers.
-/

namespace OMA.S_oeis_a302983

theorem main :
    ∀ n : ℕ, 3 < n → ∃ x y z w : ℕ, n = x ^ 2 + 2 * y ^ 2 + 2 ^ z + 3 * 2 ^ w := by
  sorry

end OMA.S_oeis_a302983
