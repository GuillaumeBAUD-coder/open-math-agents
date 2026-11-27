import OMAReductions.R_Erdos319_erdos_319_variants_lb_R1
import Mathlib

/-! Harmonic deficit: each omitted denominator in [B, N] contributes at least 1/N, and the sum of 1/i over [B, N] is at most log(N/(B-1)) by comparing 1/i with log i - log (i-1). -/

open Finset

namespace OMA.P2bErdos319H2
theorem term_le (i : ℕ) (hi : 2 ≤ i) :
    (1 : ℝ) / i ≤ Real.log i - Real.log ((i - 1 : ℕ) : ℝ) := by
  have hi' : (2 : ℝ) ≤ i := by exact_mod_cast hi
  have hc : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hc]
  have hpos : 0 < ((i : ℝ) - 1) / i := by apply div_pos <;> linarith
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (by linarith) (by linarith)] at h
  have e : ((i : ℝ) - 1) / i - 1 = -(1 / i) := by field_simp; ring
  linarith

theorem telescope (B : ℕ) : ∀ N, B - 1 ≤ N →
    ∑ i ∈ Ioc (B - 1) N, (Real.log i - Real.log ((i - 1 : ℕ) : ℝ)) =
      Real.log N - Real.log ((B - 1 : ℕ) : ℝ) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [sum_Ioc_succ_top hN, ih]
    simp

theorem harmonic (B N : ℕ) (hB : 2 ≤ B) (hBN : B ≤ N) :
    ∑ i ∈ Icc B N, (1 : ℝ) / i ≤ Real.log N - Real.log ((B : ℝ) - 1) := by
  have hI : Icc B N = Ioc (B - 1) N := by
    ext x; simp only [mem_Icc, mem_Ioc]; omega
  have hc : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [← hc, ← telescope B N (by omega), hI]
  apply sum_le_sum
  intro i hi
  rw [mem_Ioc] at hi
  exact term_le i (by omega)

end OMA.P2bErdos319H2

open OMA.P2bErdos319H2 in
theorem OMA.solution : OMA.R_Erdos319_erdos_319_variants_lb_R1.H2 := by
  unfold OMA.R_Erdos319_erdos_319_variants_lb_R1.H2
  intro B N S hB hBN hS hsum
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB1 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hsumR : ∑ i ∈ S, (1 : ℝ) / i = 1 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hsum
    simpa using this
  have hsplit := sum_sdiff hS (f := fun i : ℕ => (1 : ℝ) / i)
  have hH := harmonic B N hB hBN
  have hlow : ((Icc B N \ S).card : ℝ) / N ≤ ∑ i ∈ Icc B N \ S, (1 : ℝ) / i := by
    rw [div_eq_mul_one_div, ← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro i hi
    have hi' := mem_Icc.mp (mem_sdiff.mp hi).1
    have hipos : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
    apply one_div_le_one_div_of_le hipos
    exact_mod_cast hi'.2
  have hcard : ((Icc B N).card : ℝ) - S.card = ((Icc B N \ S).card : ℝ) := by
    rw [card_sdiff_of_subset hS, Nat.cast_sub (card_le_card hS)]
  rw [hcard, Real.log_div hN.ne' hB1.ne']
  linarith
