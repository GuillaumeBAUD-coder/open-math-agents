import OMAStatements.S_oeis_a060903
import Mathlib

namespace OMA.A060903Proof

open Real

theorem sigma_le (n : ℕ) (hn : 1 ≤ n) :
    ((∑ d ∈ n.divisors, d : ℕ) : ℝ) ≤ n * (1 + Real.log n) := by
  rw [show (∑ d ∈ n.divisors, d) = ∑ d ∈ n.divisors, n / d from (Nat.sum_div_divisors n id).symm]
  push_cast
  have h1 : ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) = ∑ d ∈ n.divisors, (n : ℝ) * (d : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd
      positivity
    rw [Nat.cast_div hd' hd0, div_eq_mul_inv]
  rw [h1, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  calc ∑ d ∈ n.divisors, (d : ℝ)⁻¹ ≤ ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (harmonic n : ℝ) := by
        rw [harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ 1 + Real.log n := harmonic_le_one_add_log n

theorem log_le (n : ℕ) (hn : 1 ≤ n) : Real.log n ≤ 2 * √n / 7 + 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
  have he : (7 : ℝ) ≤ exp 2 := by
    have := exp_one_gt_d9
    have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    rw [h2]; nlinarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hs (exp_pos 2))
  rw [Real.log_div hs.ne' (exp_pos 2).ne', Real.log_exp, Real.log_sqrt hn'.le] at h1
  have h3 : √(n : ℝ) / exp 2 ≤ √n / 7 := div_le_div_of_nonneg_left hs.le (by norm_num) he
  linarith

theorem fin_check : ∀ n < 100, 13 ≤ n → ((∑ d ∈ n.divisors, d) + 1) ^ 2 * 100 ≤ 36 * n ^ 3 := by
  decide

theorem key (n : ℕ) (hn : 13 ≤ n) :
    ((∑ d ∈ n.divisors, d : ℕ) : ℝ) + 1 ≤ 3 / 5 * n * √n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hss : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
  by_cases h100 : n < 100
  · have h := fin_check n h100 hn
    have h' : (((∑ d ∈ n.divisors, d : ℕ) : ℝ) + 1) ^ 2 * 100 ≤ 36 * (n : ℝ) ^ 3 := by
      exact_mod_cast h
    set A := ((∑ d ∈ n.divisors, d : ℕ) : ℝ) + 1
    have hA : 0 ≤ A := by positivity
    by_contra hc
    push Not at hc
    have hb : 0 ≤ 3 / 5 * (n : ℝ) * √n := by positivity
    have := mul_self_lt_mul_self hb hc
    have e : (3 / 5 * (n : ℝ) * √n) * (3 / 5 * (n : ℝ) * √n) = 9 / 25 * (n : ℝ) ^ 3 := by
      have : (3 / 5 * (n : ℝ) * √n) * (3 / 5 * (n : ℝ) * √n) = 9 / 25 * (n : ℝ) ^ 2 * √n ^ 2 := by
        ring
      rw [this, hss]; ring
    nlinarith
  · push Not at h100
    have hsig := sigma_le n (by omega)
    have hlog := log_le n (by omega)
    have h10 : (10 : ℝ) ≤ √n := by
      rw [Real.le_sqrt (by norm_num) hn'.le]
      have : (100 : ℝ) ≤ n := by exact_mod_cast h100
      linarith
    have hn100 : (100 : ℝ) ≤ n := by exact_mod_cast h100
    have : (n : ℝ) * (1 + Real.log n) ≤ n * (3 + 2 * √n / 7) := by
      apply mul_le_mul_of_nonneg_left _ hn'.le; linarith
    nlinarith

end OMA.A060903Proof

open OMA.A060903Proof Real in
theorem OMA.solution : type_of% @OMA.S_oeis_a060903.main := by
  intro n hn
  have hk := key n (by omega)
  have hpi : π ^ 2 ≤ 10 := by nlinarith [pi_lt_d2, pi_pos]
  have hpi0 : 0 < π ^ 2 := by positivity
  have hb : 3 / 5 * (n : ℝ) * √n ≤ 6 * n * √n / π ^ 2 := by
    rw [le_div_iff₀ hpi0]
    have : 0 ≤ (n : ℝ) * √n := by positivity
    nlinarith
  have hf : (∑ d ∈ n.divisors, d) + 1 ≤ ⌊6 * (n : ℝ) * √n / π ^ 2⌋₊ := by
    apply Nat.le_floor
    push_cast at hk ⊢
    linarith
  omega
