import Mathlib

namespace OMA.S_oeis_a166102

/-- OEIS A166100(`n`): sum of positive integers `1 ≤ i ≤ 2*n + 1` with Jacobi symbol `J(i, 2*n + 1) = 1`. -/
def a166100 (n : ℕ) : ℕ :=
  ∑ i ∈ (Finset.Icc 1 (2 * n + 1)).filter (fun (i : ℕ) => jacobiSym (i : ℤ) (2 * n + 1) = 1), i

/-- OEIS A166104 membership: positive integers whose prime factors are all congruent to `3` or `5` mod `6`. -/
def IsA166104 (m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p % 6 = 3 ∨ p % 6 = 5

/-- OEIS A166102 Conjecture: An odd positive integer `k` satisfies `k ∤ A166100((k - 1) / 2)`
if and only if `k = 3 * m^2` for some `m` in `A166104` (so `A166102(n) = 3 * A166103(n)`). -/
theorem main :
    ∀ k : ℕ, Odd k →
      (¬ k ∣ a166100 ((k - 1) / 2) ↔ ∃ m : ℕ, IsA166104 m ∧ k = 3 * m ^ 2) := by
  sorry

end OMA.S_oeis_a166102
