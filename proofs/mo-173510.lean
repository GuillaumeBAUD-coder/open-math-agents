import OMAStatements.S_mo_173510
import Mathlib

/-! For `a₁ = 4`, `d = 13` the term `2344 = 4 + 180 * 13` exceeds `φ(13) * 13² = 2028`,
is not prime, and `4688` is not a sum of two primes congruent to `4 (mod 13)`. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_173510.main) := by
  intro h
  have comp : ∀ x : ℕ, (∃ c ∈ Finset.range 70, 2 ≤ c ∧ c < x ∧ x % c = 0) → ¬ x.Prime := by
    rintro x ⟨c, -, h2, hx, hm⟩ hp
    exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hm) h2 hx hp
  have key : ∀ i ∈ Finset.range 361,
      (∃ c ∈ Finset.range 70, 2 ≤ c ∧ c < 4 + i * 13 ∧ (4 + i * 13) % c = 0) ∨
      (∃ c ∈ Finset.range 70, 2 ≤ c ∧ c < 4 + (360 - i) * 13 ∧ (4 + (360 - i) * 13) % c = 0) := by
    decide +kernel
  have htot : Nat.totient 13 = 12 := by
    rw [Nat.totient_prime (by norm_num)]
  have h1 := h 4 13 (by norm_num) (by norm_num) (by norm_num) 180 (by rw [htot]; norm_num)
  rcases h1 with hp | ⟨i, j, hi, hj, hs⟩
  · exact absurd hp (by norm_num)
  · have hi' : i < 361 := by omega
    have hj' : j = 360 - i := by omega
    subst hj'
    rcases key i (Finset.mem_range.2 hi') with k | k
    · exact comp _ k hi
    · exact comp _ k hj
