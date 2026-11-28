import Mathlib

/-!
# A236462: Primes p with prime(p) + 4 and prime(p) + 6 both prime

Source: https://oeis.org/A236462
Credit: @gblacher2

`prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)` in Mathlib's
0-indexed convention. The entry states that, according to the conjecture in A236460 (Zhi-Wei Sun),
the sequence should have infinitely many terms.
-/

namespace OMA.S_oeis_a236462

/-- `prime k`: the `k`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- There are infinitely many primes `p` such that `prime(p) + 4` and `prime(p) + 6` are both
prime. -/
theorem main : {p : ℕ | p.Prime ∧ (prime p + 4).Prime ∧ (prime p + 6).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a236462
