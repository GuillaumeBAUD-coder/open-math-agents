import OMAReductions.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1
import Mathlib

-- Step Erdos165.erdos_165.variants.conjecture.R1.H1.R1.H2: hypothesis H2 of reduction Erdos165.erdos_165.variants.conjecture.R1.H1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Analytic inversion. Take `ε = η / 2` and `N = ⌈(1/2 - η) k² / log k⌉`. Then
`N ≤ k²`, so `log N ≤ 2 log k` and `N log N ≤ (1 - 2η) k² + 2 log k`. Since
`(1 + η/2)² (1 - 2η) ≤ 1 - η` and `log k < k ≤ η k² / 10` for large `k`, we get
`(1 + ε)² N log N < k²`, i.e. `(1 + ε) √(N log N) < k`. Also `N ≥ (1/2 - η) k ≥ n0`. -/

namespace P4E165

theorem eps_bound {η : ℝ} (hη : 0 < η) : (1 + η / 2) ^ 2 * (1 - 2 * η) ≤ 1 - η := by
  have e : (1 + η / 2) ^ 2 * (1 - 2 * η) = 1 - η - (7 / 4) * η ^ 2 - η ^ 3 / 2 := by ring
  rw [e]
  have h2 := pow_pos hη 2
  have h3 := pow_pos hη 3
  linarith

theorem eps_bound2 {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) : (1 + η / 2) ^ 2 ≤ 2 := by
  nlinarith

end P4E165

open P4E165 in
theorem OMA.solution : OMA.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1.H2 := by
  intro η hη hη2
  refine ⟨η / 2, by positivity, fun n0 => ?_⟩
  have hc : 0 < (1 : ℝ) / 2 - η := by linarith
  refine ⟨⌈(n0 : ℝ) / ((1 : ℝ) / 2 - η)⌉₊ + ⌈10 / η⌉₊ + 3, fun k hk => ?_⟩
  have hk1 : ((⌈(n0 : ℝ) / ((1 : ℝ) / 2 - η)⌉₊ + ⌈10 / η⌉₊ + 3 : ℕ) : ℝ) ≤ k := by
    exact_mod_cast hk
  push_cast at hk1
  have hA := Nat.le_ceil ((n0 : ℝ) / ((1 : ℝ) / 2 - η))
  have hB := Nat.le_ceil (10 / η)
  have hA0 := Nat.cast_nonneg (α := ℝ) ⌈(n0 : ℝ) / ((1 : ℝ) / 2 - η)⌉₊
  have hB0 := Nat.cast_nonneg (α := ℝ) ⌈10 / η⌉₊
  have hk3 : (3 : ℝ) ≤ k := by linarith
  have hkη : 10 / η ≤ k := by linarith
  have hkn : (n0 : ℝ) / ((1 : ℝ) / 2 - η) ≤ k := by linarith
  have hkpos : (0 : ℝ) < k := by linarith
  have hL1 : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hkpos]
    have := Real.exp_one_lt_d9
    linarith
  have hLk : Real.log k < k := by
    have := Real.log_le_sub_one_of_pos hkpos
    linarith
  have hLpos : 0 < Real.log k := by linarith
  have hx0 : 0 < ((1 : ℝ) / 2 - η) * ((k : ℝ) ^ 2 / Real.log k) := by positivity
  have hxk : ((1 : ℝ) / 2 - η) * k ≤ ((1 : ℝ) / 2 - η) * ((k : ℝ) ^ 2 / Real.log k) := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [le_div_iff₀ hLpos]
    nlinarith
  have hxle : ((1 : ℝ) / 2 - η) * ((k : ℝ) ^ 2 / Real.log k) ≤ (k : ℝ) ^ 2 / 2 := by
    have h1 : (k : ℝ) ^ 2 / Real.log k ≤ (k : ℝ) ^ 2 := div_le_self (by positivity) hL1
    have h2 : 0 ≤ (k : ℝ) ^ 2 / Real.log k := by positivity
    nlinarith
  have hxL : ((1 : ℝ) / 2 - η) * ((k : ℝ) ^ 2 / Real.log k) * Real.log k =
      ((1 : ℝ) / 2 - η) * (k : ℝ) ^ 2 := by
    field_simp
  generalize hxdef : ((1 : ℝ) / 2 - η) * ((k : ℝ) ^ 2 / Real.log k) = x at hx0 hxk hxle hxL ⊢
  generalize hLdef : Real.log k = L at hL1 hLk hLpos hxL ⊢
  refine ⟨⌈x⌉₊, ?_, Nat.le_ceil x, ?_⟩
  · have h1 : (n0 : ℝ) ≤ x := by
      have := (div_le_iff₀ hc).mp hkn
      linarith
    exact_mod_cast h1.trans (Nat.le_ceil x)
  · have hNx : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    have hxN : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    generalize hNdef : (⌈x⌉₊ : ℝ) = N at hNx hxN ⊢
    have hN1 : 1 ≤ N := by
      have hN0 : 0 < N := lt_of_lt_of_le hx0 hxN
      rw [← hNdef] at hN0 ⊢
      have : 0 < ⌈x⌉₊ := by exact_mod_cast hN0
      exact_mod_cast this
    have hNk : N ≤ (k : ℝ) ^ 2 := by nlinarith
    have hlogk2 : Real.log ((k : ℝ) ^ 2) = 2 * L := by
      rw [Real.log_pow, hLdef]; push_cast; ring
    have hlogN : Real.log N ≤ 2 * L := by
      rw [← hlogk2]
      exact Real.log_le_log (by linarith) hNk
    have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hprod : N * Real.log N ≤ (x + 1) * (2 * L) :=
      mul_le_mul hNx.le hlogN hlogN0 (by linarith)
    have heps : (1 + η / 2) ^ 2 * (1 - 2 * η) ≤ 1 - η := eps_bound hη
    have heps2 : (1 + η / 2) ^ 2 ≤ 2 := eps_bound2 hη hη2
    have hmain : (1 + η / 2) ^ 2 * (N * Real.log N) < (k : ℝ) ^ 2 := by
      have h1 : (1 + η / 2) ^ 2 * (N * Real.log N) ≤ (1 + η / 2) ^ 2 * ((x + 1) * (2 * L)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      have h2 : (x + 1) * (2 * L) = (1 - 2 * η) * (k : ℝ) ^ 2 + 2 * L := by
        have : (x + 1) * (2 * L) = 2 * (x * L) + 2 * L := by ring
        rw [this, hxL]; ring
      rw [h2] at h1
      have h3 : 10 * (k : ℝ) ≤ η * (k : ℝ) ^ 2 := by
        have := (div_le_iff₀ hη).mp hkη
        nlinarith
      have h4 := mul_le_mul_of_nonneg_right heps (sq_nonneg (k : ℝ))
      have h5 := mul_le_mul_of_nonneg_right heps2 (show 0 ≤ 2 * L by linarith)
      linarith
    have hsq := Real.sqrt_lt_sqrt (by positivity) hmain
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      Real.sqrt_sq hkpos.le] at hsq
    exact hsq
