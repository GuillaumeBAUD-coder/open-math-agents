import OMAStatements.S_oeis_a273871
import Mathlib

/-!
# OEIS A273871: primes `p` with `(p-1)^2 + 1 ∣ 4^(p-1) - 1`

**Conjecture 1.** `4^(p-1) - 1` divides `(4^(p-1))^k - 1 = (4^k)^(p-1) - 1`, so the divisibility
for `k = 1` implies it for every `k`; the converse is the case `k = 1`.

**Conjecture 2.** For a Fermat prime `p = 2^(2^m) + 1` put `B = p - 1 = 2^(2^m)`.
Since `2^m ≥ m + 1`, write `2^m = m + 1 + s`. Then

  `4^B = 2^(2B) = 2^(2^m · 4 · 2^s) = ((B^2)^2)^(2^s)`,

so `4^B - 1` is divisible by `(B^2)^2 - 1 = (B^2 + 1)(B^2 - 1)`.
-/

open OMA.S_oeis_a273871

namespace OMA.A273871

/-- Conjecture 1. -/
lemma part1 (p : ℕ) :
    InSeq p ↔ (p.Prime ∧ ∀ k : ℕ, (p - 1) ^ 2 + 1 ∣ (4 ^ k) ^ (p - 1) - 1) := by
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun k => ?_⟩
    have h1 : 4 ^ (p - 1) - 1 ∣ (4 ^ (p - 1)) ^ k - 1 := by
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (4 ^ (p - 1)) 1 k
    rw [← pow_mul, mul_comm, pow_mul] at h1
    exact h.trans h1
  · rintro ⟨hp, h⟩
    exact ⟨hp, by simpa using h 1⟩

/-- `A + 1 ∣ A^2 - 1` in `ℕ`. -/
lemma succ_dvd_sq_sub_one (A : ℕ) (hA : 1 ≤ A) : A + 1 ∣ A ^ 2 - 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, A = c + 1 := ⟨A - 1, by omega⟩
  refine ⟨c, ?_⟩
  have : (c + 1) ^ 2 = (c + 1 + 1) * c + 1 := by ring
  omega

/-- The divisibility behind Conjecture 2, with `B = 2^(2^m)`. -/
lemma fermat_part (m : ℕ) : (2 ^ 2 ^ m) ^ 2 + 1 ∣ 4 ^ (2 ^ 2 ^ m) - 1 := by
  obtain ⟨s, hs⟩ : ∃ s, 2 ^ m = m + 1 + s :=
    ⟨2 ^ m - (m + 1), by have := @Nat.lt_two_pow_self m; omega⟩
  -- `4^B = ((B^2)^2)^(2^s)`
  have key : 4 ^ (2 ^ 2 ^ m) = (((2 ^ 2 ^ m) ^ 2) ^ 2) ^ (2 ^ s) := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    have hB : 2 ^ 2 ^ m = 2 ^ m * 2 * 2 ^ s := by
      conv_lhs => rw [hs]
      rw [pow_add, pow_succ]
    rw [h4, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    rw [hB]
    ring
  rw [key]
  have h1 : ((2 ^ 2 ^ m) ^ 2) ^ 2 - 1 ∣ (((2 ^ 2 ^ m) ^ 2) ^ 2) ^ (2 ^ s) - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (((2 ^ 2 ^ m) ^ 2) ^ 2) 1 (2 ^ s)
  exact (succ_dvd_sq_sub_one ((2 ^ 2 ^ m) ^ 2) (by positivity : 0 < (2 ^ 2 ^ m) ^ 2)).trans h1

end OMA.A273871

open OMA.A273871 in
theorem OMA.solution : type_of% @OMA.S_oeis_a273871.main := by
  refine ⟨part1, fun m hm => ⟨hm, ?_⟩⟩
  rw [Nat.fermatNumber, Nat.add_sub_cancel]
  exact fermat_part m
