import OMAReductions.R_Erdos244_erdos_244_variants_Romanoff_R1
import Mathlib

-- Step Erdos244.erdos_244.variants.Romanoff.R1.H1: hypothesis H1 of reduction Erdos244.erdos_244.variants.Romanoff.R1
-- Credit: @ivillar
-- H1: for C > 1, #{(p, k) : p prime, p + C^k < x} ≥ c x for large x.
--
-- Proof: with m = (x - 1) / 2 and K = log_C m, every pair (p, k) with p ≤ m prime and k ≤ K
-- is counted (p + C^k ≤ 2m < x), so the count is at least π(m) (K + 1). Chebyshev's bound
-- π(m) log m ≥ m log 2 - log(m + 1) (Mathlib's Chebyshev.pi_ge), log y ≤ y / 20 for large y
-- (log = o(id)) and (K + 1) log C > log m give π(m) (K + 1) ≥ m / (2 log C) ≥ x / (8 log C).

open Real Finset

namespace OMA.Romanoff244

lemma count_lower (C x : ℕ) (hC : 1 < C) (hm0 : (x - 1) / 2 ≠ 0) :
    (Nat.primesLE ((x - 1) / 2) ×ˢ
        Finset.range (Nat.log C ((x - 1) / 2) + 1)).card
      ≤ ((Finset.range x ×ˢ Finset.range x).filter
          (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x)).card := by
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE] at hq ⊢
  obtain ⟨⟨hp, hpp⟩, hk⟩ := hq
  have hCK : C ^ Nat.log C ((x - 1) / 2) ≤ (x - 1) / 2 := Nat.pow_log_le_self C hm0
  have hCk : C ^ q.2 ≤ C ^ Nat.log C ((x - 1) / 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hklt : q.2 < C ^ q.2 := Nat.lt_pow_self hC
  refine ⟨⟨by omega, by omega⟩, hpp, by omega⟩

theorem romanoff_lower (C : ℕ) (hC : 1 < C) : ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
    c * x ≤ (((Finset.range x ×ˢ Finset.range x).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x)).card : ℝ) := by
  have hlC : 0 < Real.log C := Real.log_pos (by exact_mod_cast hC)
  have hlo := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 20 by norm_num)
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hlo
  refine ⟨1 / (8 * Real.log C), by positivity, 2 * (⌈Y⌉₊ + 8) + 1, ?_⟩
  intro x hx
  have hm8 : 8 ≤ (x - 1) / 2 := by omega
  have hmY : Y ≤ (((x - 1) / 2 : ℕ) : ℝ) := by
    have h1 : ⌈Y⌉₊ ≤ (x - 1) / 2 := by omega
    exact (Nat.le_ceil Y).trans (by exact_mod_cast h1)
  have hcount := count_lower C x hC (by omega)
  have hpi := Chebyshev.pi_ge ((x - 1) / 2)
  have hxm : x ≤ 2 * ((x - 1) / 2) + 2 := by omega
  set m := (x - 1) / 2 with hm
  set K := Nat.log C m with hK
  rw [Finset.card_product, Finset.card_range, Nat.primesLE_card_eq_primeCounting] at hcount
  have hm8r : (8 : ℝ) ≤ m := by exact_mod_cast hm8
  have hmpos : (0 : ℝ) < m := by linarith
  have hl2 := Real.log_two_gt_d9
  have hL8 : Real.log 8 ≤ Real.log m := Real.log_le_log (by norm_num) hm8r
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hL : 2 < Real.log m := by linarith
  have hLm1 : Real.log (m + 1) ≤ (m + 1) / 20 := by
    have h := hY (m + 1) (by linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos (show (0 : ℝ) < m + 1 by linarith)] at h
    linarith [le_abs_self (Real.log (m + 1))]
  -- (K + 1) log C > log m
  have hKlog : Real.log m < (K + 1) * Real.log C := by
    have h1 : m < C ^ (K + 1) := Nat.lt_pow_succ_log_self hC m
    have h2 : (m : ℝ) < (C : ℝ) ^ (K + 1) := by exact_mod_cast h1
    have := Real.log_lt_log hmpos h2
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  -- π m * log m ≥ m / 2
  have hpiL : (m : ℝ) / 2 ≤ Nat.primeCounting m * Real.log m := by
    have := (div_le_iff₀ (by linarith : (0 : ℝ) < Real.log m)).mp hpi
    nlinarith
  have hpi0 : (0 : ℝ) ≤ Nat.primeCounting m := Nat.cast_nonneg _
  have hmain : (m : ℝ) / 2 ≤ Nat.primeCounting m * (K + 1) * Real.log C := by nlinarith
  have hcount' : ((Nat.primeCounting m * (K + 1) : ℕ) : ℝ) ≤
      (((Finset.range x ×ˢ Finset.range x).filter
        (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x)).card : ℝ) := by
    exact_mod_cast hcount
  push_cast at hcount'
  have hxr : (x : ℝ) ≤ 2 * m + 2 := by exact_mod_cast hxm
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

end OMA.Romanoff244

theorem OMA.solution : OMA.R_Erdos244_erdos_244_variants_Romanoff_R1.H1 := by
  unfold OMA.R_Erdos244_erdos_244_variants_Romanoff_R1.H1
  exact fun C hC => OMA.Romanoff244.romanoff_lower C hC
