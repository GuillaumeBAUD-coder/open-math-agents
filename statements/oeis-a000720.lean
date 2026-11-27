import Mathlib

/-!
# A000720: pi(n), the number of primes <= n.

Source: https://oeis.org/A000720
Credit: @rabdelaal

OEIS A000720 records that the second Hardy-Littlewood conjecture, `pi(x) + pi(y) >=
pi(x + y)` for integers `x` and `y` with `min{x, y} >= 2`, is known to hold for `(x, y)`
sufficiently large (Udrescu 1975). This states that finite threshold.
-/

namespace OMA.S_oeis_a000720

/-- The second Hardy-Littlewood conjecture holds for all sufficiently large `x, y`
(Udrescu 1975; recorded in OEIS A000720). -/
theorem main : ∃ N : ℕ, ∀ x y : ℕ, N ≤ x → N ≤ y →
    Nat.primeCounting x + Nat.primeCounting y ≥ Nat.primeCounting (x + y) := by
  sorry

end OMA.S_oeis_a000720
