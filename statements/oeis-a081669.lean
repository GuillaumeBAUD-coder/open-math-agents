import Mathlib

/-!
# A081669: Expansion of exp(2x) + exp(x) * BesselI_0(2x)

Source: https://oeis.org/A081669
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Expansion of exp(2x) + exp(x) * BesselI_0(2x), with exponential generating function
coefficients a(n) = 2^n + Sum_{m=0..floor(n/2)} binomial(n, 2m) * binomial(2m, m).
Conjecture: n*a(n) + (-6*n+5)*a(n-1) + (9*n-17)*a(n-2) + 4*(n-1)*a(n-3) + 12*(-n+3)*a(n-4) = 0.
-/

namespace OMA.S_oeis_a081669

def a (n : ℕ) : ℤ :=
  (2 : ℤ) ^ n +
    ∑ m ∈ Finset.range (n / 2 + 1),
      (Nat.choose n (2 * m) : ℤ) * (Nat.choose (2 * m) m : ℤ)

theorem main :
    ∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * a n +
      (-6 * (n : ℤ) + 5) * a (n - 1) +
      (9 * (n : ℤ) - 17) * a (n - 2) +
      4 * ((n : ℤ) - 1) * a (n - 3) +
      12 * (-(n : ℤ) + 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a081669
