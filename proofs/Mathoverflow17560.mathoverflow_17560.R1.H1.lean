import OMAReductions.R_Mathoverflow17560_mathoverflow_17560_R1
import Mathlib

-- Step Mathoverflow17560.mathoverflow_17560.R1.H1: hypothesis H1 of reduction
-- Mathoverflow17560.mathoverflow_17560.R1
-- Credit: @ivillar. Write x = a/b in lowest terms; m^b = 2^a forces a >= 0 and m = 2^k, so b divides a and
-- b = 1.

/-! A rational exponent with 2^x natural is a natural number. -/

theorem OMA.solution : OMA.R_Mathoverflow17560_mathoverflow_17560_R1.H1 := by
  unfold OMA.R_Mathoverflow17560_mathoverflow_17560_R1.H1
  rintro x ⟨q, rfl⟩ ⟨m, hm⟩
  set a := q.num with ha
  set b := q.den with hb
  have hb0 : 0 < b := q.den_pos
  have hqb : (q : ℝ) * b = a := by
    have := Rat.mul_den_eq_num q
    exact_mod_cast this
  have hpow : (m : ℝ) ^ b = (2 : ℝ) ^ a := by
    rw [← hm, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), hqb, Real.rpow_intCast]
  have ha0 : 0 ≤ a := by
    by_contra hneg
    push Not at hneg
    have hlt : (2 : ℝ) ^ a < 1 := zpow_lt_one_of_neg₀ (by norm_num) hneg
    have hpos : (0 : ℝ) < (2 : ℝ) ^ a := zpow_pos (by norm_num) a
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hpow
      simp [zero_pow hb0.ne'] at hpow
      linarith
    · have : (1 : ℝ) ≤ (m : ℝ) ^ b := one_le_pow₀ (by exact_mod_cast h0)
      linarith
  obtain ⟨t, ht⟩ : ∃ t : ℕ, a = t := ⟨a.toNat, (Int.toNat_of_nonneg ha0).symm⟩
  have hnat : m ^ b = 2 ^ t := by
    rw [ht, zpow_natCast] at hpow
    exact_mod_cast hpow
  have hdvd : m ∣ 2 ^ t := hnat ▸ dvd_pow_self m hb0.ne'
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hk, ← pow_mul] at hnat
  have hkb : k * b = t := Nat.pow_right_injective le_rfl hnat
  have hcop : Nat.Coprime a.natAbs b := q.reduced
  rw [ht, Int.natAbs_natCast] at hcop
  have hb1 : b = 1 := by
    have : b ∣ t := ⟨k, by rw [← hkb, mul_comm]⟩
    exact Nat.Coprime.eq_one_of_dvd hcop.symm this
  refine ⟨t, ?_⟩
  have hq : (q : ℝ) = (a : ℝ) := by
    have := hqb
    rw [hb1, Nat.cast_one, mul_one] at this
    exact this
  rw [hq, ht]
  push_cast
  rfl
