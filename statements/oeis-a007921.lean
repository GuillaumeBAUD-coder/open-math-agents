import Mathlib.Data.Nat.Prime.Basic

/-!
# A007921: Numbers that are not the difference of two primes

Source: https://oeis.org/A007921
Credit: @MMexicann
-/

namespace OMA.S_oeis_a007921

-- The sequence ranges over positive integers, so nonprimality of `k + 2` is compositeness.
theorem main : ∀ k : ℕ, 0 < k →
    ((¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p = q + k) ↔ Odd k ∧ ¬ (k + 2).Prime) := by
  sorry

end OMA.S_oeis_a007921
