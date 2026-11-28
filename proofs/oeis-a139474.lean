import OMAStatements.S_oeis_a139474
import Mathlib

namespace OMA.A139474Proof

open OMA.S_oeis_a139474

/-- `prime(1) = 2`. -/
lemma prime_one : prime 1 = 2 := by
  simp [prime, Nat.nth_prime_zero_eq_two]

/-- `a(1) = b(1) = 1`. -/
lemma a_one : a 1 = 1 := by
  simp [a, prime_one, b]

/-- The conjecture fails at `n = 1`: `2^2 - 1 = 3` is prime but does not divide `a(1) = 1`. -/
theorem main_disproof :
    ¬ (∀ n : ℕ, 1 ≤ n → ((2 ^ prime n - 1 : ℤ) ∣ a n ↔ Nat.Prime (2 ^ prime n - 1))) := by
  intro h
  have h1 := (h 1 le_rfl).mpr (by rw [prime_one]; norm_num)
  rw [a_one, prime_one] at h1
  norm_num at h1

end OMA.A139474Proof

open OMA.A139474Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a139474.main) := main_disproof
