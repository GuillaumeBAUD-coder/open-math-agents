import OMAReductions.R_Erdos1104_erdos_1104_variants_lower_R1
import Mathlib

-- Step Erdos1104.erdos_1104.variants.lower.R1.H3: hypothesis H3 of reduction Erdos1104.erdos_1104.variants.lower.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! With `a = 1/(1-ε)`, `γ = (a² - 1)/4` and `δ = (a² - 1)/(4a²)`, take `k = ⌊a √(n log n)⌋`.
Then `(1-ε) √n / √(log n) * k ≤ n` directly, and with `L = log n`, `x = √(n L)`:
`log k ≤ log a + (L + log L)/2` and `k² ≥ a² n L - 2 a x`, so the target follows once
`log a`, `(log L)/2` and `a x / n` are each at most `γ L / 3`, which holds for large `n`. -/

namespace P4E1104

theorem log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
  rw [Real.log_sqrt hy.le] at h1
  linarith

theorem le_sqrt_of_sq_le {t y : ℝ} (ht : 0 ≤ t) (h : t ^ 2 ≤ y) : t ≤ Real.sqrt y := by
  rw [show t = Real.sqrt (t ^ 2) from (Real.sqrt_sq ht).symm]
  exact Real.sqrt_le_sqrt h

theorem ineq (a γ c n L x k la lL lk : ℝ)
    (hn : 0 < n) (hc0 : 0 ≤ c) (hc : c * a ^ 2 = 1 / 2 + γ) (hc2 : c ≤ 1 / 2)
    (hx2 : x ^ 2 = n * L) (hk1 : a * x - 1 ≤ k) (hk1' : 0 ≤ a * x - 1)
    (hlk : lk ≤ la + (L + lL) / 2) (hla : la ≤ γ * L / 3) (hlL : lL ≤ 2 * (γ * L / 3))
    (hax : a * x ≤ γ * (n * L) / 3) :
    n * lk ≤ c * k ^ 2 := by
  have h3 : (a * x - 1) ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hk1' hk1 2
  have hsq : (a * x - 1) ^ 2 = a ^ 2 * (n * L) - 2 * (a * x) + 1 := by rw [← hx2]; ring
  have hk2 : a ^ 2 * (n * L) - 2 * (a * x) ≤ k ^ 2 := by linarith
  have h4 : c * (a ^ 2 * (n * L) - 2 * (a * x)) ≤ c * k ^ 2 := mul_le_mul_of_nonneg_left hk2 hc0
  have h5 : c * (2 * (a * x)) ≤ a * x := by nlinarith
  have h6 : n * lk ≤ n * (la + (L + lL) / 2) := mul_le_mul_of_nonneg_left hlk hn.le
  have h7 : n * la ≤ n * (γ * L / 3) := mul_le_mul_of_nonneg_left hla hn.le
  have h8 : n * lL ≤ n * (2 * (γ * L / 3)) := mul_le_mul_of_nonneg_left hlL hn.le
  have h9 : c * (a ^ 2 * (n * L)) = (1 / 2 + γ) * (n * L) := by rw [← hc]; ring
  have h10 : c * (a ^ 2 * (n * L) - 2 * (a * x)) =
      c * (a ^ 2 * (n * L)) - c * (2 * (a * x)) := by ring
  have h11 : n * (la + (L + lL) / 2) = n * la + n * L / 2 + n * lL / 2 := by ring
  have h12 : n * (γ * L / 3) = γ * (n * L) / 3 := by ring
  have h13 : n * (2 * (γ * L / 3)) = 2 * (γ * (n * L) / 3) := by ring
  have h14 : (1 / 2 + γ) * (n * L) = n * L / 2 + γ * (n * L) := by ring
  linarith

end P4E1104

set_option maxHeartbeats 1000000 in
open P4E1104 in
theorem OMA.solution : OMA.R_Erdos1104_erdos_1104_variants_lower_R1.H3 := by
  intro ε hε hε1
  have h1ε : 0 < 1 - ε := by linarith
  set a : ℝ := 1 / (1 - ε) with ha
  have ha1 : 1 < a := by rw [ha, lt_div_iff₀ h1ε]; linarith
  have haε : (1 - ε) * a = 1 := by rw [ha]; exact mul_one_div_cancel h1ε.ne'
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < a ^ 2 := by positivity
  set γ : ℝ := (a ^ 2 - 1) / 4 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; nlinarith
  have hdpos : 0 < (a ^ 2 - 1) / (4 * a ^ 2) := div_pos (by nlinarith) (by positivity)
  refine ⟨(a ^ 2 - 1) / (4 * a ^ 2), hdpos, fun K => ?_⟩
  set c : ℝ := 1 / 2 - (a ^ 2 - 1) / (4 * a ^ 2) with hcdef
  have hq : (a ^ 2 - 1) / (4 * a ^ 2) * a ^ 2 = (a ^ 2 - 1) / 4 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ ha2.ne']
  have hc : c * a ^ 2 = 1 / 2 + γ := by rw [hcdef, sub_mul, hq, hγ]; ring
  have hc2 : c ≤ 1 / 2 := by linarith
  have hc0 : 0 ≤ c := by
    by_contra h
    have : c * a ^ 2 < 0 := mul_neg_of_neg_of_pos (by linarith) ha2
    linarith
  set M : ℝ := max (max (9 / γ ^ 2) (3 * Real.log a / γ)) 1 with hM
  rw [Filter.eventually_atTop]
  refine ⟨⌈Real.exp M⌉₊ + ⌈9 * a ^ 2 / γ ^ 2⌉₊ + (K + 1) ^ 2, fun n hn => ?_⟩
  have hn' : ((⌈Real.exp M⌉₊ + ⌈9 * a ^ 2 / γ ^ 2⌉₊ + (K + 1) ^ 2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast hn
  push_cast at hn'
  have hc1 := Nat.le_ceil (Real.exp M)
  have hc2' := Nat.le_ceil (9 * a ^ 2 / γ ^ 2)
  have hc10 := Nat.cast_nonneg (α := ℝ) ⌈Real.exp M⌉₊
  have hc20 := Nat.cast_nonneg (α := ℝ) ⌈9 * a ^ 2 / γ ^ 2⌉₊
  have hK0 : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ 2 := by positivity
  have hnexp : Real.exp M ≤ n := by linarith
  have hn9 : 9 * a ^ 2 / γ ^ 2 ≤ n := by linarith
  have hnK : ((K : ℝ) + 1) ^ 2 ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos M) hnexp
  have hLM : M ≤ Real.log n := by rw [Real.le_log_iff_exp_le hnpos]; exact hnexp
  have hL1 : 1 ≤ Real.log n := le_trans (le_max_right _ _) hLM
  have hL9 : 9 / γ ^ 2 ≤ Real.log n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLM
  have hLa : 3 * Real.log a / γ ≤ Real.log n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLM
  generalize hLdef : Real.log n = L at hL1 hL9 hLa ⊢
  have hL0 : 0 < L := by linarith
  have hnL : (n : ℝ) ≤ n * L := le_mul_of_one_le_right hnpos.le hL1
  set x : ℝ := Real.sqrt ((n : ℝ) * L) with hx
  have hx2 : x ^ 2 = n * L := Real.sq_sqrt (by positivity)
  have hxprod : x = Real.sqrt n * Real.sqrt L := by rw [hx, Real.sqrt_mul hnpos.le]
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxK : (K : ℝ) + 1 ≤ x := le_sqrt_of_sq_le (by positivity) (by linarith)
  have hxa : 3 * a / γ ≤ x := by
    apply le_sqrt_of_sq_le (by positivity)
    have : (3 * a / γ) ^ 2 = 9 * a ^ 2 / γ ^ 2 := by ring
    rw [this]; linarith
  have hax : x ≤ a * x := le_mul_of_one_le_left hx0 ha1.le
  have hfloor := Nat.floor_le (show 0 ≤ a * x by positivity)
  have hfloor2 := Nat.lt_floor_add_one (a * x)
  generalize hk : ⌊a * x⌋₊ = k at hfloor hfloor2
  have hK1 : (1 : ℝ) ≤ (K : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) K
    linarith
  refine ⟨k, ?_, ?_, ?_⟩
  · have h1 : (K : ℝ) < k + 1 := by linarith
    have h2 : K < k + 1 := by exact_mod_cast h1
    omega
  · have hkpos : (0 : ℝ) < k := by linarith
    have hlogk : Real.log k ≤ Real.log a + (L + Real.log L) / 2 := by
      have h1 : Real.log k ≤ Real.log (a * x) := Real.log_le_log hkpos hfloor
      have h2 : Real.log (a * x) = Real.log a + Real.log x :=
        Real.log_mul ha0.ne' (by linarith)
      have h3 : Real.log x = (Real.log n + Real.log L) / 2 := by
        rw [hx, Real.log_sqrt (by positivity), Real.log_mul hnpos.ne' hL0.ne']
      rw [hLdef] at h3
      linarith
    have hlogL : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt hL0
    have hsqrtL : 3 / γ ≤ Real.sqrt L := by
      apply le_sqrt_of_sq_le (by positivity)
      have : (3 / γ) ^ 2 = 9 / γ ^ 2 := by ring
      rw [this]; exact hL9
    have hsL : Real.sqrt L ≤ γ * L / 3 := by
      have hs2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
      have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
      have h3 : 3 ≤ γ * Real.sqrt L := by
        have := (div_le_iff₀ hγ0).mp hsqrtL
        linarith
      have h4 : 3 * Real.sqrt L ≤ γ * Real.sqrt L * Real.sqrt L :=
        mul_le_mul_of_nonneg_right h3 hs0
      have h5 : γ * Real.sqrt L * Real.sqrt L = γ * L := by
        rw [mul_assoc, ← sq, hs2]
      linarith
    have hloga : Real.log a ≤ γ * L / 3 := by
      have := (div_le_iff₀ hγ0).mp hLa
      linarith
    have hax3 : a * x ≤ γ * (n * L) / 3 := by
      rw [← hx2]
      have h1 : 3 * a ≤ γ * x := by
        have := (div_le_iff₀ hγ0).mp hxa
        linarith
      have h2 : 3 * a * x ≤ γ * x * x := mul_le_mul_of_nonneg_right h1 hx0
      have h3 : γ * x * x = γ * x ^ 2 := by ring
      linarith
    exact ineq a γ c n L x k (Real.log a) (Real.log L) (Real.log k) hnpos hc0 hc hc2 hx2
      (by linarith) (by linarith) hlogk hloga (by linarith) hax3
  · have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
    have h1 : (1 - ε) * Real.sqrt n / Real.sqrt L * k ≤
        (1 - ε) * Real.sqrt n / Real.sqrt L * (a * x) :=
      mul_le_mul_of_nonneg_left hfloor (by positivity)
    have h2 : (1 - ε) * Real.sqrt n / Real.sqrt L * (a * x) = n := by
      rw [hxprod]
      have e : (1 - ε) * Real.sqrt n / Real.sqrt L * (a * (Real.sqrt n * Real.sqrt L)) =
          ((1 - ε) * a) * (Real.sqrt n * Real.sqrt n) * (Real.sqrt L / Real.sqrt L) := by ring
      rw [e, haε, Real.mul_self_sqrt hnpos.le, div_self hsL.ne', one_mul, mul_one]
    linarith
