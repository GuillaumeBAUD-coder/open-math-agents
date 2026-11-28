import OMAStatements.S_oeis_a175406
import Mathlib

/-!
Counterexample n = N = 1121626023352383, K = 777451915729368: the floor of (N + 1/2) log 2 is K,
but (1 + 1/N)^K > 2, so a(N) ≤ K - 1. Both facts need log 2 to about 33 digits. The partial sum
with 110 terms of log 2 = Σ 2^-(i+1)/(i+1) is within 2^-110 of log 2, and
log(1 + y) ≥ y - y^2/2 + y^3/3 - y^4/(1 - y) for y = 1/N; both come from
Real.abs_log_sub_add_sum_range_le. The remaining comparisons are exact rational arithmetic.
-/

namespace R175406
open OMA.S_oeis_a175406

theorem log2_bounds : (69314718055994530941723212145817579082413229 / 100000000000000000000000000000000000000000000 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (693147180559945309417232121458177331568087801 / 1000000000000000000000000000000000000000000000 : ℝ) := by
  have t : |(2⁻¹ : ℝ)| = 2⁻¹ := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : ℝ)| < 1 by rw [t]; norm_num) 110
  rw [t, show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, Real.log_inv, ← sub_eq_add_neg] at z
  obtain ⟨h1, h2⟩ := abs_le.mp z
  generalize Real.log 2 = L at h1 h2 ⊢
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1 h2
  norm_num at h1 h2
  constructor <;> linarith

theorem log1_lower : (11144534577255301341912389384338529688093344083369 / 12500000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1 / (1121626023352383 : ℝ)) := by
  have t : |(-(1 / (1121626023352383 : ℝ)))| = 1 / 1121626023352383 := by
    rw [abs_neg, abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le
    (show |(-(1 / (1121626023352383 : ℝ)))| < 1 by rw [t]; norm_num) 3
  rw [t, sub_neg_eq_add] at z
  obtain ⟨h1, -⟩ := abs_le.mp z
  generalize Real.log (1 + 1 / (1121626023352383 : ℝ)) = L at h1 ⊢
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1
  norm_num at h1
  linarith

end R175406

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a175406.main) := by
  intro h
  have hN := h 1121626023352383 (by norm_num)
  obtain ⟨hlo, hhi⟩ := R175406.log2_bounds
  have hl1 := R175406.log1_lower
  have hcast : ((1121626023352383 : ℕ) : ℝ) = (1121626023352383 : ℝ) := by norm_num
  have hfloor : Nat.floor ((((1121626023352383 : ℕ) : ℝ) + 1 / 2) * Real.log 2) =
      777451915729368 := by
    rw [hcast, Nat.floor_eq_iff (show (0 : ℝ) ≤ ((1121626023352383 : ℝ) + 1 / 2) * Real.log 2 from
      mul_nonneg (by norm_num) (by linarith))]
    push_cast
    constructor <;> linarith
  rw [hfloor] at hN
  have hpow : (2 : ℝ) < (1 + (1 : ℝ) / ((1121626023352383 : ℕ) : ℝ)) ^ 777451915729368 := by
    rw [hcast]
    have hpos : (0 : ℝ) < (1 + 1 / (1121626023352383 : ℝ)) ^ 777451915729368 :=
      pow_pos (by norm_num) _
    rw [← Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 2) hpos, Real.log_pow]
    clear hpos
    generalize Real.log (1 + 1 / (1121626023352383 : ℝ)) = L at hl1 ⊢
    push_cast
    linarith
  have hle : OMA.S_oeis_a175406.a 1121626023352383 ≤ 777451915729367 := by
    unfold OMA.S_oeis_a175406.a
    refine csSup_le ⟨0, by simp⟩ ?_
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    by_contra hcon
    have hk' : 777451915729368 ≤ k := by omega
    have h1 : (1 : ℝ) ≤ 1 + 1 / ((1121626023352383 : ℕ) : ℝ) :=
      le_add_of_nonneg_right (by positivity)
    have hmono := pow_le_pow_right₀ h1 hk'
    exact lt_irrefl (2 : ℝ) (lt_of_lt_of_le hpow (hmono.trans hk))
  omega
