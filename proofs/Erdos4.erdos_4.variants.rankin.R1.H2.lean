import OMAReductions.R_Erdos4_erdos_4_variants_rankin_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # `x ≤ π(x)²` for `x ≥ 4096`

Chebyshev's bound `(x log 2 - log (x + 1)) / log x ≤ π(x)` is at least `√x` once
`√x log x + log (x + 1) ≤ x log 2`. With `s = x ^ (1/4) ≥ 8` and `log x = 4 log s ≤ 4 (s - 1)` this
is `4 s³ + 4 s + 1 ≤ 0.69 s⁴`.
-/

namespace OMA4

lemma sqrt_le_pi (x : ℕ) (hx : 4096 ≤ x) :
    Real.sqrt (x : ℝ) ≤ (Nat.primeCounting x : ℝ) := by
  have hxR : (4096 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  set s : ℝ := Real.sqrt (Real.sqrt (x : ℝ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Real.sqrt (x : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = (x : ℝ) := by
    have h : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [h, hs2, Real.sq_sqrt (by linarith)]
  have hs8 : 8 ≤ s := by
    by_contra h
    push_neg at h
    have h2 : s ^ 2 < 64 := by nlinarith
    have h4 : s ^ 4 < 4096 := by nlinarith [sq_nonneg s]
    linarith
  have hlogx : Real.log (x : ℝ) = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]
    norm_num
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog1 : Real.log ((x : ℝ) + 1) ≤ Real.log 2 + Real.log (x : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hpi := Chebyshev.pi_ge x
  have hA : 8 * s ^ 3 ≤ s ^ 4 := by nlinarith [pow_nonneg hs0 3]
  have hB : 64 * s ≤ s ^ 3 := by nlinarith [mul_nonneg hs0 hs0]
  have h1 : s ^ 2 * Real.log (x : ℝ) ≤ 4 * s ^ 3 := by
    rw [hlogx]
    have := mul_le_mul_of_nonneg_left hlogs (sq_nonneg s)
    nlinarith [sq_nonneg s]
  have h2 : (x : ℝ) * 0.69 ≤ (x : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 (by linarith)
  have hkey : s ^ 2 * Real.log (x : ℝ) ≤ (x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1) := by
    have h3 : Real.log ((x : ℝ) + 1) ≤ 1 + 4 * (s - 1) := by
      rw [hlogx] at hlog1
      linarith
    linarith
  rw [← hs2]
  exact le_trans ((le_div_iff₀ hlogx_pos).2 hkey) hpi

end OMA4

theorem OMA.solution : OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2 := by
  refine ⟨4096, fun x hx => ?_⟩
  have h := OMA4.sqrt_le_pi x hx
  have hsq : (x : ℝ) ≤ (Nat.primeCounting x : ℝ) ^ 2 := by
    calc (x : ℝ) = Real.sqrt (x : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg x)).symm
      _ ≤ (Nat.primeCounting x : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  exact_mod_cast hsq
