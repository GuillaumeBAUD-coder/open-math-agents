import Mathlib

/-!
# A271983: The smaller of a pair n, m such that phi(n) = phi(m) and no other k has phi(k) = phi(n)

Source: https://oeis.org/A271983
Credit: @niclorusso

Conjecture (in the comments of A271983): If phi(x) = N has exactly two solutions, x = n and x = m,
say (see A007366), it is conjectured that one of n and m is odd and the other even.

Conventions:
* phi is Euler's totient (`Nat.totient`); solutions x range over the positive integers.
* "phi(x) = N has exactly two solutions n and m" means n /= m, phi(n) = phi(m) = N, and every
  positive x with phi(x) = N is n or m.
-/

namespace OMA.S_oeis_a271983

/-- The conjecture on A271983: if `phi(x) = N` has exactly the two positive solutions `n /= m`,
then one of them is odd and the other even. -/
theorem main : ∀ N n m : ℕ, 0 < n → 0 < m → n ≠ m → Nat.totient n = N → Nat.totient m = N →
    (∀ x : ℕ, 0 < x → Nat.totient x = N → x = n ∨ x = m) →
    (Odd n ∧ Even m) ∨ (Even n ∧ Odd m) := by
  sorry

end OMA.S_oeis_a271983
