import OMAReductions.R_mse_5049175_R1

/-!
Step `mse-5049175.R1.H1`: `f_1 ∣ f_n`, `f_2 ∣ f_n` for even `n`, `f_3 ∣ f_n` for odd `n ≥ 3`.

With `f_n(a) = (B_{n+1}(a+1) - B_{n+1}(0))/(n+1)`:
* `f_n(0) = 0` by `B_k(1+x) = B_k(x) + k x^(k-1)`, and `f_n(-1) = 0` trivially;
* `f_n(-1/2) = 0` for even `n ≥ 2`, since `B_{n+1}(1/2) = -B_{n+1}(1/2)` by
  `B_k(1-x) = (-1)^k B_k(x)` and `B_{n+1}(0) = 0`;
* `f_n' = B_n(x+1)` (as `B_{k+1}' = (k+1) B_k`), which vanishes at `0` and `-1` for odd `n ≥ 3`,
  so `0` and `-1` are double roots (`Polynomial.one_lt_rootMultiplicity_iff_isRoot`).
`f_1`, `f_2`, `f_3` are computed explicitly from the coefficients of the Bernoulli polynomials,
and the linear factors are pairwise coprime.
-/

namespace OMA.R_mse_5049175_R1.Step1

open Polynomial OMA.S_mse_5049175

theorem f_eval (n : ℕ) (a : ℚ) : (f n).eval a =
    (1 / ((n : ℚ) + 1)) * ((Polynomial.bernoulli (n + 1)).eval (a + 1) -
      (Polynomial.bernoulli (n + 1)).eval 0) := by
  simp [f, eval_smul, eval_comp]

theorem f_eval_zero (n : ℕ) (hn : 1 ≤ n) : (f n).eval 0 = 0 := by
  rw [f_eval, zero_add]
  have h := Polynomial.bernoulli_eval_one_add (n + 1) 0
  rw [add_zero] at h
  rw [h]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp

theorem f_eval_neg_one (n : ℕ) : (f n).eval (-1) = 0 := by
  simp [f_eval]

theorem f_eval_half (n : ℕ) (hn : 2 ≤ n) (he : Even n) : (f n).eval (-1 / 2) = 0 := by
  rw [f_eval]
  have h1 := Polynomial.bernoulli_eval_one_sub (n + 1) (1 / 2)
  have hodd : Odd (n + 1) := he.add_one
  rw [hodd.neg_one_pow] at h1
  have h0 : (Polynomial.bernoulli (n + 1)).eval 0 = 0 := by
    rw [Polynomial.bernoulli_eval_zero]; exact bernoulli_eq_zero_of_odd hodd (by omega)
  have h2 : (-1 / 2 : ℚ) + 1 = 1 / 2 := by norm_num
  have h3 : (1 : ℚ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h3] at h1
  rw [h2, h0]
  have : (Polynomial.bernoulli (n + 1)).eval (1 / 2) = 0 := by linarith
  rw [this]; ring

theorem f_deriv_eval (n : ℕ) (a : ℚ) :
    (derivative (f n)).eval a = (Polynomial.bernoulli n).eval (a + 1) := by
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  simp only [f, derivative_smul, derivative_sub, derivative_C, sub_zero, derivative_comp,
    Polynomial.derivative_bernoulli_add_one, eval_smul, eval_mul, eval_comp, derivative_add,
    derivative_X, derivative_one, add_zero, eval_one, one_mul, eval_add, eval_X, smul_eq_mul]
  rw [eval_natCast]
  field_simp

theorem f_deriv_zero (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) : (derivative (f n)).eval 0 = 0 := by
  rw [f_deriv_eval, zero_add]
  have h := Polynomial.bernoulli_eval_one_add n 0
  rw [add_zero] at h
  rw [h, Polynomial.bernoulli_eval_zero, bernoulli_eq_zero_of_odd ho (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp

theorem f_deriv_neg_one (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) :
    (derivative (f n)).eval (-1) = 0 := by
  rw [f_deriv_eval, neg_add_cancel, Polynomial.bernoulli_eval_zero,
    bernoulli_eq_zero_of_odd ho (by omega)]

theorem lin_dvd (p : ℚ[X]) (a : ℚ) (h : p.eval a = 0) : X - C a ∣ p :=
  dvd_iff_isRoot.mpr h

theorem sq_dvd (p : ℚ[X]) (a : ℚ) (h0 : p.eval a = 0) (h1 : (derivative p).eval a = 0) :
    (X - C a) ^ 2 ∣ p := by
  by_cases hp : p = 0
  · simp [hp]
  rw [← le_rootMultiplicity_iff hp]
  exact (one_lt_rootMultiplicity_iff_isRoot hp).2 ⟨h0, h1⟩

theorem cop (a b : ℚ) (h : a ≠ b) : IsCoprime (X - C a) (X - C b) :=
  isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h))

theorem bpoly_eval (n : ℕ) (r : ℚ) : (Polynomial.bernoulli n).eval r =
    ∑ i ∈ Finset.range (n + 1), _root_.bernoulli (n - i) * (n.choose i) * r ^ i := by
  rw [Polynomial.bernoulli_def, eval_finsetSum]
  simp [eval_monomial]

theorem f1_eq : f 1 = C (1 / 2) * ((X - C 0) * (X - C (-1))) := by
  apply Polynomial.funext; intro r
  rw [f_eval, bpoly_eval, bpoly_eval]
  simp [Finset.sum_range_succ, _root_.bernoulli_one]
  ring

theorem f2_eq : f 2 = C (1 / 3) * ((X - C 0) * (X - C (-1)) * (X - C (-1 / 2))) := by
  apply Polynomial.funext; intro r
  rw [f_eval, bpoly_eval, bpoly_eval]
  simp [Finset.sum_range_succ, _root_.bernoulli_one, bernoulli_eq_bernoulli'_of_ne_one, Nat.choose]
  ring

theorem f3_eq : f 3 = C (1 / 4) * ((X - C 0) ^ 2 * (X - C (-1)) ^ 2) := by
  apply Polynomial.funext; intro r
  rw [f_eval, bpoly_eval, bpoly_eval]
  simp [Finset.sum_range_succ, _root_.bernoulli_one, bernoulli_eq_bernoulli'_of_ne_one, Nat.choose,
    bernoulli'_four]
  ring

theorem part1 (n : ℕ) (hn : 1 ≤ n) : f 1 ∣ f n := by
  rw [f1_eq, C_mul_dvd (by norm_num)]
  exact (cop 0 (-1) (by norm_num)).mul_dvd (lin_dvd _ _ (f_eval_zero n hn))
    (lin_dvd _ _ (f_eval_neg_one n))

theorem part2 (n : ℕ) (hn : 2 ≤ n) (he : Even n) : f 2 ∣ f n := by
  rw [f2_eq, C_mul_dvd (by norm_num)]
  have hc : IsCoprime ((X - C 0) * (X - C (-1))) (X - C (-1 / 2 : ℚ)) :=
    IsCoprime.mul_left (cop _ _ (by norm_num)) (cop _ _ (by norm_num))
  exact hc.mul_dvd ((cop 0 (-1) (by norm_num)).mul_dvd (lin_dvd _ _ (f_eval_zero n (by omega)))
    (lin_dvd _ _ (f_eval_neg_one n))) (lin_dvd _ _ (f_eval_half n hn he))

theorem part3 (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) : f 3 ∣ f n := by
  rw [f3_eq, C_mul_dvd (by norm_num)]
  exact ((cop 0 (-1) (by norm_num)).pow).mul_dvd
    (sq_dvd _ _ (f_eval_zero n (by omega)) (f_deriv_zero n hn ho))
    (sq_dvd _ _ (f_eval_neg_one n) (f_deriv_neg_one n hn ho))

end OMA.R_mse_5049175_R1.Step1

theorem OMA.solution : OMA.R_mse_5049175_R1.H1 :=
  ⟨OMA.R_mse_5049175_R1.Step1.part1, OMA.R_mse_5049175_R1.Step1.part2,
    OMA.R_mse_5049175_R1.Step1.part3⟩
