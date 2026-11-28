import Mathlib

/-!
# A093345: a(n) = n! * {1 + Sum[i=1..n, 1/i*Sum(j=0..i-1, 1/j!)]}.

Source: https://oeis.org/A093345
Credit: @agchua

R. J. Mathar (May 30 2014), in the formula section of A093345:
  Conjecture: a(n) -2*n*a(n-1) +(n^2-2)*a(n-2) -(n-2)^2*a(n-3)=0.
The sequence has offset 0 (a(0) = 1). The recurrence uses a(n-3), so the conjecture is stated
for n ≥ 3. The definition is computed in ℚ (its values are integers).
-/

namespace OMA.S_oeis_a093345

/-- A093345(n) = n! * (1 + Sum_{i=1..n} (1/i) * Sum_{j=0..i-1} 1/j!). -/
def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) *
    (1 + ∑ i ∈ Finset.Icc 1 n, (1 / (i : ℚ)) * ∑ j ∈ Finset.range i, 1 / (j.factorial : ℚ))

/-- Mathar's conjecture: for n ≥ 3, a(n) - 2n a(n-1) + (n^2-2) a(n-2) - (n-2)^2 a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n - 2 * (n : ℚ) * a (n - 1) + ((n : ℚ) ^ 2 - 2) * a (n - 2)
      - ((n : ℚ) - 2) ^ 2 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a093345
