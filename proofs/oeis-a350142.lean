import OMAStatements.S_oeis_a350142
import Mathlib

/-!
# A350142: with `m = 2 ^ k + 1`, `τ(m - 2) = τ(m - 1) - 1` iff `τ(m - 2) = k`

Here `m - 1 = 2 ^ k` has exactly `k + 1` divisors, so `τ(m - 1) - 1 = k` and the two conditions
are literally the same.
-/

namespace OMA.S_oeis_a350142

/-- `2 ^ k` has `k + 1` divisors. -/
lemma tau_two_pow (k : ℕ) : tau (2 ^ k) = k + 1 := by
  unfold tau
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]

end OMA.S_oeis_a350142

open OMA.S_oeis_a350142 in
theorem OMA.solution : type_of% @OMA.S_oeis_a350142.main := by
  intro k
  show tau (2 ^ k + 1 - 2) = tau (2 ^ k + 1 - 1) - 1 ↔ tau (2 ^ k + 1 - 2) = k
  rw [Nat.add_sub_cancel, tau_two_pow, Nat.add_sub_cancel]
