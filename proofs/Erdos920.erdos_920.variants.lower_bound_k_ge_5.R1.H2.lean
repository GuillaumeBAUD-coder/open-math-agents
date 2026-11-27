import OMAReductions.R_Erdos920_erdos_920_variants_lower_bound_k_ge_5_R1
import Mathlib

-- Step Erdos920.erdos_920.variants.lower_bound_k_ge_5.R1.H2: hypothesis H2 of reduction Erdos920.erdos_920.variants.lower_bound_k_ge_5.R1
-- Credit: @ivillar (original proof).
-- Strategy. For large n take m = ceil(mu t) with t = n^(1/d) (log n)^(a/d) and mu^d = 2/C. Then m <= n,
-- so log m <= log n and C m^d / (log m)^a >= 2n > n, hence n < R m and F n >= n/m >= n/(2 mu t).

open Filter Asymptotics in
theorem OMA.solution : OMA.R_Erdos920_erdos_920_variants_lower_bound_k_ge_5_R1.H2 := by
  intro d hd a C ha hC R F hR hF
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hade : a / (d : ℝ) = a * (1 / (d : ℝ)) := by ring
  rw [hade]
  set e : ℝ := 1 / (d : ℝ) with he
  have he0 : 0 < e := by positivity
  have hed : e * d = 1 := by rw [he]; field_simp
  have he1 : e < 1 := by
    rw [he, div_lt_one hd0]
    linarith
  set μ : ℝ := (2 / C) ^ e with hμ
  have hμ0 : 0 < μ := by positivity
  have hμd : μ ^ d = 2 / C := by
    rw [hμ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hed, Real.rpow_one]
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp hR
  have hn_tend : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he0).comp hn_tend
  have hlo : (fun n : ℕ => Real.log n ^ (a * e)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - e)) :=
    (isLittleO_log_rpow_rpow_atTop (a * e) (by linarith : (0 : ℝ) < 1 - e)).comp_tendsto hn_tend
  have ev1 := hlo.bound (by positivity : (0 : ℝ) < 1 / (2 * μ))
  have ev2 := hpow.eventually_ge_atTop (((M0 : ℝ) + 3) / μ + 1 / μ)
  apply IsBigO.of_bound (2 * μ)
  filter_upwards [ev1, ev2, eventually_ge_atTop 3] with n h1 h2 h3
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h3
  have hn0 : (0 : ℝ) < n := by linarith
  set L := Real.log n with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hL0 : 0 < L := by linarith
  have hLa : 1 ≤ L ^ (a * e) := Real.one_le_rpow hL1 (by positivity)
  have hne0 : 0 < (n : ℝ) ^ e := Real.rpow_pos_of_pos hn0 e
  have h1' : L ^ (a * e) ≤ 1 / (2 * μ) * (n : ℝ) ^ (1 - e) := by
    have h1a : ‖L ^ (a * e)‖ = L ^ (a * e) := Real.norm_of_nonneg (by positivity)
    have h1b : ‖(n : ℝ) ^ (1 - e)‖ = (n : ℝ) ^ (1 - e) := Real.norm_of_nonneg (by positivity)
    rw [h1a, h1b] at h1
    exact h1
  set t := (n : ℝ) ^ e * L ^ (a * e) with ht
  have ht0 : 0 < t := by positivity
  have hte : (n : ℝ) ^ e ≤ t := by
    rw [ht]
    exact le_mul_of_one_le_right hne0.le hLa
  set m := ⌈μ * t⌉₊ with hm
  have hm1 : μ * t ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < μ * t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hμt : (M0 : ℝ) + 4 ≤ μ * t := by
    have : μ * (((M0 : ℝ) + 3) / μ + 1 / μ) ≤ μ * t :=
      mul_le_mul_of_nonneg_left (h2.trans hte) hμ0.le
    rw [mul_add, mul_div_cancel₀ _ hμ0.ne', mul_div_cancel₀ _ hμ0.ne'] at this
    linarith
  have hmM0 : M0 ≤ m := by
    have : (M0 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hm3 : (3 : ℝ) ≤ m := by linarith [(Nat.cast_nonneg M0 : (0 : ℝ) ≤ M0)]
  have hm2' : (m : ℝ) ≤ 2 * μ * t := by linarith
  have hmn : (m : ℝ) ≤ n := by
    have : 2 * μ * t ≤ n := by
      have hsplit : (n : ℝ) = (n : ℝ) ^ e * (n : ℝ) ^ (1 - e) := by
        rw [← Real.rpow_add hn0, add_sub_cancel, Real.rpow_one]
      calc 2 * μ * t = 2 * μ * ((n : ℝ) ^ e * L ^ (a * e)) := by rw [ht]
        _ ≤ 2 * μ * ((n : ℝ) ^ e * (1 / (2 * μ) * (n : ℝ) ^ (1 - e))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h1' hne0.le
        _ = (n : ℝ) ^ e * (n : ℝ) ^ (1 - e) := by field_simp
        _ = n := hsplit.symm
    linarith
  have hlogm0 : 0 < Real.log m := Real.log_pos (by linarith)
  have hlogm : Real.log m ≤ L := Real.log_le_log (by linarith) hmn
  have hRm := hM0 m hmM0
  have htd : t ^ d = (n : ℝ) * L ^ a := by
    rw [ht, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, hed, Real.rpow_one,
      ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, mul_assoc, hed, mul_one]
  have hmd : (2 / C) * ((n : ℝ) * L ^ a) ≤ (m : ℝ) ^ d := by
    rw [← hμd, ← htd, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hm1 d
  have hLa0 : 0 < L ^ a := Real.rpow_pos_of_pos hL0 a
  have hla0 : 0 < Real.log m ^ a := Real.rpow_pos_of_pos hlogm0 a
  have hlam : Real.log m ^ a ≤ L ^ a := Real.rpow_le_rpow hlogm0.le hlogm ha.le
  have key : 2 * (n : ℝ) ≤ C * (m : ℝ) ^ d / Real.log m ^ a := by
    calc 2 * (n : ℝ) = C * ((2 / C) * ((n : ℝ) * L ^ a)) / L ^ a := by
          field_simp
      _ ≤ C * (m : ℝ) ^ d / L ^ a := by
          apply div_le_div_of_nonneg_right _ hLa0.le
          exact mul_le_mul_of_nonneg_left hmd hC.le
      _ ≤ C * (m : ℝ) ^ d / Real.log m ^ a :=
          div_le_div_of_nonneg_left (by positivity) hla0 hlam
  have hnR : n < R m := by
    have : (n : ℝ) < R m := by linarith
    exact_mod_cast this
  have hFn := hF n m (by omega) hnR
  have hm0 : (0 : ℝ) < m := by linarith
  have hgoal : (n : ℝ) ^ (1 - e) / L ^ (a * e) ≤ 2 * μ * (F n : ℝ) := by
    have hq : (n : ℝ) ^ (1 - e) / L ^ (a * e) = (n : ℝ) / t := by
      rw [ht, Real.rpow_sub hn0, Real.rpow_one]
      field_simp
    rw [hq]
    calc (n : ℝ) / t = 2 * μ * ((n : ℝ) / (2 * μ * t)) := by field_simp
      _ ≤ 2 * μ * ((n : ℝ) / m) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_left hn0.le hm0 hm2'
      _ ≤ 2 * μ * (F n : ℝ) := mul_le_mul_of_nonneg_left hFn (by positivity)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact hgoal
