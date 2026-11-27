import OMAReductions.R_Erdos16_erdos_16_variant_romanoff_R1
import Mathlib

-- Step Erdos16.erdos_16.variant.romanoff.R1.H1: hypothesis H1 of reduction Erdos16.erdos_16.variant.romanoff.R1
-- Credit: @ivillar
-- H1: the number of representations n = 2^k + p (k ≥ 1, p an odd prime, n ≤ x) is at least c x.
--
-- Proof: with m = x / 2 and K = log₂ m, the map (k, p) ↦ (2^k + p, k) injects
-- [1, K] × {odd primes ≤ m} into the counted pairs, so the sum is at least K (π(m) - 1).
-- Chebyshev's bound π(m) ≥ (m log 2 - log(m + 1)) / log m (Mathlib's Chebyshev.pi_ge),
-- log y ≤ y / 20 for large y (log = o(id)) and K ≥ log m / 2 give K (π(m) - 1) ≥ m / 4 ≥ x / 16.

open Real Finset

namespace OMA.Romanoff16

lemma count_lower (x : ℕ) :
    Nat.log 2 (x / 2) * ((Finset.range (x / 2 + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).card
      ≤ ∑ n ∈ Finset.range (x + 1),
        ((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
          n - 2 ^ k ≠ 2)).card := by
  rw [← Finset.card_sigma]
  have hcard : ((Finset.Icc 1 (Nat.log 2 (x / 2))) ×ˢ
      ((Finset.range (x / 2 + 1)).filter (fun p => p.Prime ∧ p ≠ 2))).card
      = Nat.log 2 (x / 2) * ((Finset.range (x / 2 + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).card := by
    rw [Finset.card_product, Nat.card_Icc]
    simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun kp => (⟨2 ^ kp.1 + kp.2, kp.1⟩ : Σ _ : ℕ, ℕ))
  · intro kp hkp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc,
      Finset.mem_filter, Finset.mem_range] at hkp
    obtain ⟨⟨hk1, hkK⟩, hpm, hpp, hp2⟩ := hkp
    have hm0 : x / 2 ≠ 0 := by
      intro h0
      rw [h0, Nat.log_zero_right] at hkK
      omega
    have h2K : 2 ^ Nat.log 2 (x / 2) ≤ x / 2 := Nat.pow_log_le_self 2 hm0
    have h2k : 2 ^ kp.1 ≤ 2 ^ Nat.log 2 (x / 2) := Nat.pow_le_pow_right (by norm_num) hkK
    have hklt : kp.1 < 2 ^ kp.1 := Nat.lt_two_pow_self
    have hp2' : 2 ≤ kp.2 := hpp.two_le
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
    refine ⟨by omega, by omega, hk1, by omega, ?_, ?_⟩
    · rwa [Nat.add_sub_cancel_left]
    · rw [Nat.add_sub_cancel_left]
      exact hp2
  · intro a _ b _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    obtain ⟨h1, h2⟩ := h
    apply Prod.ext h2
    rw [h2] at h1
    omega

lemma card_odd_primes (m : ℕ) (hm : 2 ≤ m) :
    ((Finset.range (m + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).card + 1 = Nat.primeCounting m := by
  have hQ : (Finset.range (m + 1)).filter (fun p => p.Prime ∧ p ≠ 2) = (Nat.primesLE m).erase 2 := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, Nat.mem_primesLE]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h3, by omega, h2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, h3, h1⟩
  rw [hQ, Finset.card_erase_add_one (Nat.mem_primesLE.mpr ⟨hm, Nat.prime_two⟩),
    Nat.primesLE_card_eq_primeCounting]

theorem romanoff_lower : ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
    c * x ≤ ∑ n ∈ Finset.range (x + 1),
      (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)).card : ℝ) := by
  have hlo := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 20 by norm_num)
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hlo
  refine ⟨1 / 16, by norm_num, 2 * (⌈Y⌉₊ + 8), ?_⟩
  intro x hx
  have hm8 : 8 ≤ x / 2 := by omega
  have hmY : Y ≤ ((x / 2 : ℕ) : ℝ) := by
    have h1 : ⌈Y⌉₊ ≤ x / 2 := by omega
    exact (Nat.le_ceil Y).trans (by exact_mod_cast h1)
  -- abbreviations
  have hcount := count_lower x
  have hQ := card_odd_primes (x / 2) (by omega)
  have hpi := Chebyshev.pi_ge (x / 2)
  set m := x / 2 with hm
  set K := Nat.log 2 m with hK
  set q := ((Finset.range (m + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).card with hq
  have hm8r : (8 : ℝ) ≤ m := by exact_mod_cast hm8
  have hmpos : (0 : ℝ) < m := by linarith
  -- logarithm estimates
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hL8 : Real.log 8 ≤ Real.log m := Real.log_le_log (by norm_num) hm8r
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hL : 2 < Real.log m := by linarith
  have hLm : Real.log m ≤ m / 20 := by
    have h := hY m hmY
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hmpos] at h
    linarith [le_abs_self (Real.log m)]
  have hLm1 : Real.log (m + 1) ≤ (m + 1) / 20 := by
    have h := hY (m + 1) (by linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos (show (0 : ℝ) < m + 1 by linarith)] at h
    linarith [le_abs_self (Real.log (m + 1))]
  -- K is at least log m / 2
  have hKlog : Real.log m / 2 ≤ K := by
    have h1 : m < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have h2 : (m : ℝ) < 2 ^ (K + 1) := by exact_mod_cast h1
    have h3 : Real.log m < (K + 1) * Real.log 2 := by
      have := Real.log_lt_log hmpos h2
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    nlinarith
  -- q * log m ≥ m / 2
  have hqL : (m : ℝ) / 2 ≤ q * Real.log m := by
    have hpi' : (m : ℝ) * Real.log 2 - Real.log (m + 1) ≤ Nat.primeCounting m * Real.log m := by
      have := (div_le_iff₀ (by linarith : (0 : ℝ) < Real.log m)).mp hpi
      exact this
    have hqr : (q : ℝ) + 1 = Nat.primeCounting m := by exact_mod_cast hQ
    rw [← hqr] at hpi'
    nlinarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hmain : (m : ℝ) / 4 ≤ K * q := by nlinarith
  have hcount' : ((K * q : ℕ) : ℝ) ≤ ∑ n ∈ Finset.range (x + 1),
      (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hcount
  push_cast at hcount'
  have hxm : (x : ℝ) ≤ 2 * m + 1 := by
    have : x ≤ 2 * m + 1 := by omega
    exact_mod_cast this
  nlinarith

end OMA.Romanoff16

theorem OMA.solution : OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H1 := by
  unfold OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H1
  exact OMA.Romanoff16.romanoff_lower
