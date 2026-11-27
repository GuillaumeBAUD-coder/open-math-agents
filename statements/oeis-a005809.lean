import Mathlib

/-!
# A005809: a(n) = binomial(3n, n).

Source: https://oeis.org/A005809
Credit: @rabdelaal

OEIS A005809 records the conjecture (Gary Detlefs, 2013) that `binomial(3n, n) = 3`
modulo `n ^ 3` iff `n` is an odd prime. For odd prime `p` this is a known generalization
of Wolstenholme's theorem (Mestrovic, Section 6, equation 35).
-/

namespace OMA.S_oeis_a005809

/-- The OEIS A005809 entry: `binomial(3n, n)`. -/
def a (n : ℕ) : ℕ := Nat.choose (3 * n) n

/-- The conjecture recorded in OEIS A005809 (Detlefs): `binomial(3n, n) ≡ 3 (mod n³)`
iff `n` is an odd prime. -/
theorem main : ∀ n ≥ 1, a n % n ^ 3 = 3 % (n ^ 3) ↔ (Nat.Prime n ∧ n % 2 = 1) := by
  sorry

end OMA.S_oeis_a005809
