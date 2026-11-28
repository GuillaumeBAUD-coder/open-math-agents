import OMAStatements.S_oeis_a016627
import Mathlib

namespace OMA.A016627Proof

open Filter Topology
open OMA.S_oeis_a016627

/-- The partial sums telescope to `H_N - H_{N / 4}`. -/
lemma key (N : ℕ) : ∑ k ∈ Finset.Icc 1 N, (T 4 k : ℝ) / k
    = (harmonic N : ℝ) - (harmonic (N / 4) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
    have hs := Nat.succ_div (a := N) (b := 4)
    by_cases h : 4 ∣ N + 1
    · rw [if_pos h] at hs
      have hm : ((N + 1) / 4) * 4 = N + 1 := Nat.div_mul_cancel h
      rw [hs, harmonic_succ] at *
      have hm' : (((N / 4 : ℕ) : ℝ) + 1) * 4 = (N : ℝ) + 1 := by exact_mod_cast hm
      simp only [T, if_pos h]
      push_cast
      have h1 : ((N : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (((N / 4 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      nlinarith [hm']
    · rw [if_neg h, add_zero] at hs
      rw [hs]
      simp only [T, if_neg h]
      push_cast
      ring

lemma tail (a r : ℕ) : (harmonic (a + r) : ℝ) - harmonic a ≤ r / (a + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← add_assoc, harmonic_succ]
    push_cast
    have : ((a : ℝ) + r + 1)⁻¹ ≤ 1 / (a + 1) := by
      rw [inv_eq_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have e : ((r : ℝ) + 1) / (a + 1) = r / (a + 1) + 1 / (a + 1) := by ring
    rw [e]
    linarith

lemma mono (a r : ℕ) : (harmonic a : ℝ) ≤ harmonic (a + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← add_assoc, harmonic_succ]
    push_cast
    have : (0 : ℝ) ≤ ((a : ℝ) + r + 1)⁻¹ := by positivity
    linarith

lemma f_lim : Tendsto (fun m : ℕ => (harmonic (4 * m) : ℝ) - harmonic m) atTop
    (𝓝 (Real.log 4)) := by
  have h1 := Real.tendsto_harmonic_sub_log
  have h2 : Tendsto (fun m : ℕ => (harmonic (4 * m) : ℝ) - Real.log ((4 * m : ℕ) : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
    h1.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 4))
  have h3 := (h2.sub h1).add_const (Real.log 4)
  rw [show Real.eulerMascheroniConstant - Real.eulerMascheroniConstant + Real.log 4
    = Real.log 4 by ring] at h3
  apply h3.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (m : ℝ) ≠ 0 := by positivity
  push_cast
  rw [Real.log_mul (by norm_num) hm']
  ring

theorem main_proof :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (T 4 k : ℝ) / k) atTop
      (𝓝 (Real.log 4)) := by
  simp_rw [key]
  have hf := f_lim.comp (Nat.tendsto_div_const_atTop (n := 4) (by norm_num))
  have hz : Tendsto (fun N : ℕ => (harmonic N : ℝ) - harmonic (4 * (N / 4))) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => (3 : ℝ) / ((N / 4 : ℕ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp
        ((tendsto_add_atTop_nat 1).comp (Nat.tendsto_div_const_atTop (n := 4) (by norm_num)))
      refine this.congr' (Eventually.of_forall fun N => ?_)
      simp
    refine squeeze_zero (fun N => ?_) (fun N => ?_) hb
    · have e : N = 4 * (N / 4) + N % 4 := (Nat.div_add_mod N 4).symm
      have := mono (4 * (N / 4)) (N % 4)
      rw [← e] at this
      linarith
    · have e : N = 4 * (N / 4) + N % 4 := (Nat.div_add_mod N 4).symm
      have ht := tail (4 * (N / 4)) (N % 4)
      rw [← e] at ht
      have hr : ((N % 4 : ℕ) : ℝ) ≤ 3 := by
        have : N % 4 ≤ 3 := by omega
        exact_mod_cast this
      refine ht.trans ?_
      push_cast
      have hq : (0 : ℝ) ≤ ((N / 4 : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have := hz.add hf
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun N => ?_)
  simp only [Function.comp]
  ring

end OMA.A016627Proof

open OMA.A016627Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a016627.main := main_proof
