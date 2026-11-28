import OMAReductions.R_Erdos727_erdos_727_variants_k_2_R1
import Mathlib

-- Step Erdos727.erdos_727.variants.k_2.R1.H2: hypothesis H2 of reduction Erdos727.erdos_727.variants.k_2.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Kummer's theorem (`Nat.factorization_choose`) computes the exponent of `p` in `C(2n, n)` as the
number of carries `p^i ≤ 2 (n mod p^i)` for `1 ≤ i ≤ log_p(2n)`. Divisibility by `W^2` is the
primewise comparison of exponents, and primes not dividing `W` impose nothing. The size
condition follows because the carry count is at most `log_p(2n)`. -/

namespace P4E727

open Finset Nat

theorem kummer (n p : ℕ) (hp : p.Prime) :
    ((2 * n).choose n).factorization p =
      ((Ico 1 (Nat.log p (2 * n) + 1)).filter (fun i ↦ p ^ i ≤ 2 * (n % p ^ i))).card := by
  rw [Nat.factorization_choose hp (show n ≤ 2 * n by omega) (Nat.lt_succ_self _)]
  have e : 2 * n - n = n := by omega
  simp only [e, ← two_mul]

end P4E727

open Finset Nat P4E727 in
theorem OMA.solution : OMA.R_Erdos727_erdos_727_variants_k_2_R1.H2 := by
  intro n hn
  dsimp only
  have hW0 : (n + 1) * (n + 2) ≠ 0 := by positivity
  have hC0 : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [← Nat.factorization_prime_le_iff_dvd (pow_ne_zero 2 hW0) hC0]
  constructor
  · intro h p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 := h p hpp
    rw [Nat.factorization_pow, kummer n p hpp] at h1
    simp only [Finsupp.smul_apply, smul_eq_mul] at h1
    refine ⟨?_, h1⟩
    have hcard : ((Ico 1 (Nat.log p (2 * n) + 1)).filter
        (fun i ↦ p ^ i ≤ 2 * (n % p ^ i))).card ≤ Nat.log p (2 * n) := by
      calc _ ≤ (Ico 1 (Nat.log p (2 * n) + 1)).card := Finset.card_filter_le _ _
        _ = Nat.log p (2 * n) := by simp
    calc p ^ (2 * ((n + 1) * (n + 2)).factorization p) ≤ p ^ (Nat.log p (2 * n)) :=
          Nat.pow_le_pow_right hpp.pos (h1.trans hcard)
      _ ≤ 2 * n := Nat.pow_log_le_self p (by omega)
  · intro h p hp
    rw [Nat.factorization_pow, kummer n p hp]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases hpW : p ∈ ((n + 1) * (n + 2)).primeFactors
    · exact (h p hpW).2
    · have hnd : ¬ p ∣ (n + 1) * (n + 2) := fun hd =>
        hpW (Nat.mem_primeFactors.mpr ⟨hp, hd, hW0⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd hnd]
      simp
