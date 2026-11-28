import OMAStatements.S_oeis_a227917
import Mathlib

/-!
# OEIS A227917: the Laplace integral for semi-increasing binary plane trees

The rising factorial expands in unsigned Stirling numbers of the first kind,
and each monomial integrates against `exp (-2x)` to `k! / 2^(k+1)` by the Gamma integral.
-/

open Finset MeasureTheory

namespace OMA.A227917

open OMA.S_oeis_a227917

theorem rising_eq (x : ℝ) (n : ℕ) :
    rising x n = ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * x ^ k := by
  induction n with
  | zero => simp [rising, Nat.stirlingFirst_zero]
  | succ n ih =>
    have hstep : rising x (n + 1) = rising x n * (x + n) := by
      simp [rising, Finset.prod_range_succ]
    have h0 : (n : ℝ) * (Nat.stirlingFirst n 0 : ℝ) = 0 := by
      cases n with
      | zero => simp
      | succ m => simp [Nat.stirlingFirst_succ_zero]
    have hS : ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * x ^ k
        = ∑ k ∈ range n, (Nat.stirlingFirst n (k + 1) : ℝ) * x ^ (k + 1)
          + (Nat.stirlingFirst n 0 : ℝ) := by
      rw [Finset.sum_range_succ']; simp
    have hT : ∑ k ∈ range (n + 1), (Nat.stirlingFirst n (k + 1) : ℝ) * x ^ (k + 1)
        = ∑ k ∈ range n, (Nat.stirlingFirst n (k + 1) : ℝ) * x ^ (k + 1) := by
      rw [Finset.sum_range_succ]
      simp [Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n)]
    have hR : ∑ k ∈ range (n + 1 + 1), (Nat.stirlingFirst (n + 1) k : ℝ) * x ^ k
        = (n : ℝ) * ∑ k ∈ range (n + 1), (Nat.stirlingFirst n (k + 1) : ℝ) * x ^ (k + 1)
          + x * ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * x ^ k := by
      rw [Finset.sum_range_succ', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      simp only [Nat.stirlingFirst_succ_zero, Nat.cast_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.stirlingFirst_succ_succ]
      push_cast
      ring
    rw [hstep, hR, hT, ih, hS]
    linear_combination h0

theorem integral_mono (k : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ k * Real.exp (-(2 * x)) = (k.factorial : ℝ) / 2 ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := 2)
    (by positivity) (by norm_num)
  rw [Real.Gamma_nat_eq_factorial] at h
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [h]
  have : ((1 : ℝ) / 2) ^ ((k : ℝ) + 1) = 1 / 2 ^ (k + 1) := by
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    simp
  rw [this]
  ring

theorem integrable_mono (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(2 * x))) (Set.Ioi 0) := by
  by_contra h
  have h1 := integral_undef h
  rw [integral_mono] at h1
  have : (0 : ℝ) < (k.factorial : ℝ) / 2 ^ (k + 1) := by positivity
  linarith

end OMA.A227917

open OMA.S_oeis_a227917 OMA.A227917 in
theorem OMA.solution : type_of% @OMA.S_oeis_a227917.main := by
  intro n _
  have hfun : (fun x : ℝ => rising x n / Real.exp (2 * x))
      = fun x => ∑ k ∈ range (n + 1),
          (Nat.stirlingFirst n k : ℝ) * (x ^ k * Real.exp (-(2 * x))) := by
    funext x
    rw [rising_eq, Real.exp_neg, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun, integral_finsetSum _ (fun k _ => (integrable_mono k).const_mul _)]
  simp only [integral_const_mul, integral_mono]
  rw [Finset.mul_sum]
  unfold trees
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h2 : (2 : ℝ) ^ (n + 1) = 2 ^ (n - k) * 2 ^ (k + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [h2]
  field_simp
