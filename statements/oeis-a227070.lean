import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Nth

namespace OMA.S_oeis_a227070

/-- The set `s(n) = {k > 0 | k^n ends with k in base 10}`, where "ends with `k`" means
`k^n ≡ k (mod 10^d)` for `d = ⌊log_10(k)⌋ + 1` (the number of base-10 digits of `k`). -/
def automorphicSet (n : ℕ) : Set ℕ :=
  {k : ℕ | 0 < k ∧ k ^ n % 10 ^ (Nat.log 10 k + 1) = k}

/-- Membership predicate for OEIS A227070: powers `n ≥ 1` whose automorphic set `s(n)` does
not occur for any smaller positive power `m < n`. -/
def IsA227070 (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → m < n → automorphicSet m ≠ automorphicSet n

/-- Membership predicate for OEIS A003592: positive integers of the form `2^i * 5^j`. -/
def IsA003592 (m : ℕ) : Prop :=
  ∃ i j : ℕ, m = 2 ^ i * 5 ^ j

/-- The 1-indexed sequence OEIS A227070. -/
noncomputable def A227070 (n : ℕ) : ℕ :=
  Nat.nth IsA227070 (n - 1)

/-- The 1-indexed sequence OEIS A003592. -/
noncomputable def A003592 (n : ℕ) : ℕ :=
  Nat.nth IsA003592 (n - 1)

/-- Conjecture (OEIS A227070): for every `n ≥ 1`, `A227070(n + 1) = A003592(n) + 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → A227070 (n + 1) = A003592 n + 1 := by
  sorry

end OMA.S_oeis_a227070
