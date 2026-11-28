import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a237275

/-- `a(n)` (OEIS A237275): the smallest positive integer `k` whose last decimal digit `k % 10`
is greater than `1` and satisfies `(k % 10) ^ n ∣ k`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k}

/-- Conjecture (OEIS A237275): `a(n) ≡ 2 (mod 10)` for all `n`. -/
theorem main : ∀ n : ℕ, a n % 10 = 2 := by
  sorry

end OMA.S_oeis_a237275
