import Mathlib

namespace OMA.S_oeis_a111489

/-- Infinitely many primes are sums of the equally indexed prime and composite. -/
theorem main :
    Set.Infinite {m : ℕ | m.Prime ∧ ∃ k : ℕ,
      m = Nat.nth Nat.Prime k + Nat.nth (fun c : ℕ => 2 ≤ c ∧ ¬ c.Prime) k} := by
  sorry

end OMA.S_oeis_a111489
