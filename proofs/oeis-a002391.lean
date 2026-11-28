import OMAStatements.S_oeis_a002391
import Mathlib

namespace OMA.A002391Proof

open OMA.S_oeis_a002391 Filter Topology

lemma partial_eq (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (T 3 k : ℝ) / k = (harmonic N : ℝ) - (harmonic (N / 3) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
    by_cases h : 3 ∣ N + 1
    · have e : (N + 1) / 3 = N / 3 + 1 := by omega
      have e2 : ((N / 3 + 1 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) / 3 := by
        have : 3 * (N / 3 + 1) = N + 1 := by omega
        rw [eq_div_iff (by norm_num)]
        exact_mod_cast (by omega : (N / 3 + 1) * 3 = N + 1)
      rw [e, harmonic_succ]
      simp only [T, if_pos h]
      push_cast
      push_cast at e2
      rw [e2]
      have : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · have e : (N + 1) / 3 = N / 3 := by omega
      rw [e]
      simp only [T, if_neg h]
      push_cast
      ring

lemma err_tendsto :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) / 3) - Real.log ((N / 3 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hm : Tendsto (fun N : ℕ => N / 3) atTop atTop := Nat.tendsto_div_const_atTop (by norm_num)
  have hinv : Tendsto (fun N : ℕ => ((N / 3 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hm)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hm1 : (1 : ℝ) ≤ ((N / 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N / 3)
    have hle : ((N / 3 : ℕ) : ℝ) ≤ (N : ℝ) / 3 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast (by omega : N / 3 * 3 ≤ N)
    have := Real.log_le_log (by linarith) hle
    linarith
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hm1' : (1 : ℝ) ≤ ((N / 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N / 3)
    set m : ℝ := ((N / 3 : ℕ) : ℝ) with hmdef
    have hm1 : (1 : ℝ) ≤ m := hm1'
    have hle : (N : ℝ) / 3 ≤ m + 1 := by
      rw [div_le_iff₀ (by norm_num)]
      have : N ≤ (N / 3 + 1) * 3 := by omega
      have : (N : ℝ) ≤ (((N / 3 + 1) * 3 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this
      rw [hmdef]; linarith
    have hpos : (0 : ℝ) < (N : ℝ) / 3 := by
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN
      positivity
    have h1 : Real.log ((N : ℝ) / 3) - Real.log m = Real.log (((N : ℝ) / 3) / m) := by
      rw [Real.log_div hpos.ne' (by linarith)]
    rw [h1]
    have h2 := Real.log_le_sub_one_of_pos (div_pos hpos (by linarith : (0 : ℝ) < m))
    have h3 : ((N : ℝ) / 3) / m - 1 ≤ m⁻¹ := by
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith), inv_mul_cancel₀ (by linarith)]
      linarith
    linarith

theorem main_proof :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (T 3 k : ℝ) / k) atTop (𝓝 (Real.log 3)) := by
  have hm : Tendsto (fun N : ℕ => N / 3) atTop atTop := Nat.tendsto_div_const_atTop (by norm_num)
  have A := Real.tendsto_harmonic_sub_log
  have B := A.comp hm
  have C := ((A.sub B).add (err_tendsto)).add_const (Real.log 3)
  simp only [sub_self, zero_add] at C
  apply C.congr'
  filter_upwards [eventually_ge_atTop 3] with N hN
  rw [partial_eq]
  have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  simp only [Function.comp]
  rw [Real.log_div hpos.ne' (by norm_num)]
  ring

end OMA.A002391Proof

open OMA.A002391Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a002391.main := main_proof
