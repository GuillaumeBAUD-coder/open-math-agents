import OMAStatements.S_oeis_a227917

open Finset MeasureTheory Set
open OMA.S_oeis_a227917

private theorem risingExpansion (x : ℝ) (n : ℕ) :
    rising x n = ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * x ^ k := by
  induction n with
  | zero => simp [rising]
  | succ n ih =>
    let g (k : ℕ) := (n : ℝ) * (Nat.stirlingFirst n k : ℝ) * x ^ k
    have hhead : g 0 = 0 := by cases n <;> simp [g]
    have htail : g (n + 1) = 0 := by
      simp [g, Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n)]
    have hshift : (∑ k ∈ range (n + 1), g (k + 1)) = ∑ k ∈ range (n + 1), g k := by
      have h := sum_range_succ' g (n + 1)
      rw [sum_range_succ g (n + 1), htail, hhead, add_zero, add_zero] at h
      exact h.symm
    have hg : (∑ k ∈ range (n + 1), g k) =
        (n : ℝ) * ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * x ^ k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      dsimp [g]
      ring
    have hx : (∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * x ^ (k + 1)) =
        x * ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * x ^ k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      rw [pow_succ]
      ring
    rw [sum_range_succ' _ (n + 1)]
    simp only [Nat.stirlingFirst_succ_zero, Nat.cast_zero, zero_mul, add_zero]
    have hProd : rising x (n + 1) = rising x n * (x + n) := by
      exact prod_range_succ _ n
    rw [hProd, ih]
    simp only [Nat.stirlingFirst_succ_succ, Nat.cast_add, Nat.cast_mul,
      add_mul, sum_add_distrib]
    change _ = (∑ k ∈ range (n + 1), g (k + 1)) +
      ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * x ^ (k + 1)
    rw [hshift, hg, hx]
    ring

private theorem integrableMoment (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k / Real.exp (2 * x)) (Ioi 0) := by
  let f (x : ℝ) := Real.exp (-x) * x ^ k
  have hf : IntegrableOn f (Ioi 0) := by
    simpa [f, Real.rpow_natCast] using
      (Real.GammaIntegral_convergent (s := (k : ℝ) + 1) (by positivity))
  have hScaled : IntegrableOn (fun x : ℝ => f (2 * x)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff f 0 (by norm_num : (0 : ℝ) < 2)).2 (by simpa using hf)
  refine IntegrableOn.congr_fun (hScaled.const_mul ((2 : ℝ) ^ k)⁻¹) ?_ measurableSet_Ioi
  intro x _
  dsimp [f]
  rw [mul_pow, div_eq_mul_inv, ← Real.exp_neg]
  calc
    _ = ((2 : ℝ) ^ k)⁻¹ * 2 ^ k * (x ^ k * Real.exp (-(2 * x))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (by positivity), one_mul]

private theorem integralMoment (k : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ k / Real.exp (2 * x)) = (k.factorial : ℝ) / 2 ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1)
    (r := 2) (by positivity) (by norm_num)
  rw [add_sub_cancel_right, Real.Gamma_nat_eq_factorial,
    show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by simp] at h
  simp only [Real.rpow_natCast, one_div, inv_pow] at h
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_comm] using h

theorem OMA.solution : type_of% @OMA.S_oeis_a227917.main := by
  intro n _
  have hExpand (x : ℝ) : rising x n / Real.exp (2 * x) =
      ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℝ) * (x ^ k / Real.exp (2 * x)) := by
    rw [risingExpansion, sum_div]
    apply sum_congr rfl
    intro k _
    exact mul_div_assoc _ _ _
  simp_rw [hExpand]
  rw [integral_finsetSum _ (fun k _ => (integrableMoment k).const_mul _)]
  simp_rw [integral_const_mul, integralMoment]
  unfold trees
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hPower : (2 : ℝ) ^ (n + 1) = 2 ^ (n - k) * 2 ^ (k + 1) := by
    rw [← pow_add]
    congr 1
    have := mem_range.mp hk
    omega
  rw [hPower]
  field_simp
