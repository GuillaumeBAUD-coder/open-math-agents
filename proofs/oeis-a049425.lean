import OMAStatements.S_oeis_a049425

/-!
Proof of OEIS A049425: differentiating the exponential generating function
series = exp.subst (X + X^2 + (1/3)*X^3) via a self-contained dPs helper yields
dPs series = (1 + 2*X + X^2) * series.
Extracting the coefficient of X^(n+2) and multiplying by (n+2)! gives Mathar's recurrence.
-/

section Proof

open PowerSeries

private noncomputable def dPs (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f

private lemma coeff_dPs (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (dPs f) = ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f := by
  simp [dPs]

private lemma dPs_C (c : ℚ) : dPs (C c) = 0 := by
  ext n
  simp [coeff_dPs]

private lemma dPs_one : dPs (1 : PowerSeries ℚ) = 0 := by
  rw [← map_one C]
  exact dPs_C 1

private lemma dPs_X : dPs (X : PowerSeries ℚ) = 1 := by
  ext n
  simp only [coeff_dPs, coeff_X, coeff_one]
  cases n <;> simp

private lemma dPs_add (f g : PowerSeries ℚ) : dPs (f + g) = dPs f + dPs g := by
  ext n
  simp only [coeff_dPs, map_add]
  ring

private lemma dPs_mul (f g : PowerSeries ℚ) : dPs (f * g) = dPs f * g + f * dPs g := by
  ext n
  rw [coeff_dPs, map_add, coeff_mul, coeff_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i f * coeff j g) (n + 1),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (dPs f) * coeff j g) n,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i f * coeff j (dPs g)) n,
    Finset.mul_sum]
  have hsplit :
      ∑ k ∈ Finset.range (n + 2),
          ((n + 1 : ℕ) : ℚ) * (coeff k f * coeff (n + 1 - k) g) =
        ∑ k ∈ Finset.range (n + 2),
          (((k : ℚ) * coeff k f) * coeff (n + 1 - k) g +
            coeff k f * (((n + 1 - k : ℕ) : ℚ) * coeff (n + 1 - k) g)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hnat : (k : ℚ) + ((n + 1 - k : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_sub_of_le hk_le
    rw [← hnat]
    ring
  rw [hsplit, Finset.sum_add_distrib]
  have h1 :
      ∑ k ∈ Finset.range (n + 2), ((k : ℚ) * coeff k f) * coeff (n + 1 - k) g =
        ∑ k ∈ Finset.range (n + 1), coeff k (dPs f) * coeff (n - k) g := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_dPs, Nat.succ_sub_succ]
  have h2 :
      ∑ k ∈ Finset.range (n + 2),
          coeff k f * (((n + 1 - k : ℕ) : ℚ) * coeff (n + 1 - k) g) =
        ∑ k ∈ Finset.range (n + 1), coeff k f * coeff (n - k) (dPs g) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coeff_dPs, Nat.sub_add_comm hk_le]
  rw [h1, h2]

private lemma dPs_sum {ι : Type*} (s : Finset ι) (g : ι → PowerSeries ℚ) :
    dPs (∑ i ∈ s, g i) = ∑ i ∈ s, dPs (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ← map_zero C, dPs_C, map_zero]
  | insert a s ha ih => simp [Finset.sum_insert ha, dPs_add, ih]

private lemma dPs_pow (f : PowerSeries ℚ) :
    ∀ d : ℕ, dPs (f ^ d) = C (d : ℚ) * f ^ (d - 1) * dPs f
  | 0 => by simp [dPs_one]
  | d + 1 => by
    rw [pow_succ, dPs_mul, dPs_pow f d]
    cases d with
    | zero => simp
    | succ m =>
      push_cast
      simp only [map_add, map_natCast, map_one, pow_succ]
      ring

end Proof

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a049425.main := by
  have hsub : HasSubst OMA.S_oeis_a049425.parameter :=
    HasSubst.of_constantCoeff_zero' (by simp [OMA.S_oeis_a049425.parameter])
  have hdparam : dPs OMA.S_oeis_a049425.parameter = 1 + 2 * X + X ^ 2 := by
    unfold OMA.S_oeis_a049425.parameter
    rw [dPs_add, dPs_add, dPs_mul, dPs_C, zero_mul, zero_add, dPs_pow, dPs_pow, dPs_X]
    have hC : C (1 / 3 : ℚ) * C ((3 : ℕ) : ℚ) = 1 := by
      rw [← map_mul]
      norm_num
    simp only [Nat.add_one_sub_one, show 3 - 1 = 2 by decide, pow_one, mul_one,
      show ((2 : ℕ) : ℚ) = 2 by norm_num, map_ofNat]
    linear_combination X ^ 2 * hC
  let P : PowerSeries ℚ := OMA.S_oeis_a049425.parameter
  have hP_factor : P = X * (1 + X + C (1 / 3 : ℚ) * X ^ 2) := by
    unfold P OMA.S_oeis_a049425.parameter
    ring
  have hP_pow_zero : ∀ d m : ℕ, m < d → coeff m (P ^ d) = 0 := fun d m hmd => by
    rw [hP_factor, mul_pow, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (X ^ d) * coeff j ((1 + X + C (1 / 3 : ℚ) * X ^ 2) ^ d)) m]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hile : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp [coeff_X_pow, show i ≠ d by omega]
  let S (N : ℕ) : PowerSeries ℚ :=
    ∑ d ∈ Finset.range (N + 1), C ((d.factorial : ℚ)⁻¹) * P ^ d
  have hS_eq : ∀ m N : ℕ, m ≤ N → coeff m OMA.S_oeis_a049425.series = coeff m (S N) := by
    intro m N hmN
    unfold OMA.S_oeis_a049425.series
    rw [coeff_subst' hsub]
    change finsum (fun d => coeff d (exp ℚ) • coeff m (P ^ d)) = coeff m (S N)
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1)) fun d hd => by
      by_contra hmem
      have hlt : m < d := by
        have := Finset.mem_range.not.mp hmem
        omega
      simp only [Function.mem_support, ne_eq] at hd
      exact hd (by simp [hP_pow_zero d m hlt])]
    dsimp [S]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [coeff_exp, coeff_C_mul, one_div]
  have hdS : ∀ k : ℕ, dPs (S (k + 1)) = S k * dPs P := fun k => by
    dsimp [S]
    rw [dPs_sum, Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, map_one, one_mul, pow_zero, dPs_one,
      add_zero]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [dPs_mul, dPs_C, zero_mul, zero_add, dPs_pow]
    have hfac : C (((d + 1).factorial : ℚ)⁻¹) * C ((d + 1 : ℕ) : ℚ) = C ((d.factorial : ℚ)⁻¹) := by
      rw [← map_mul]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      have hf : (d.factorial : ℚ) ≠ 0 := by positivity
      have hd1 : (d : ℚ) + 1 ≠ 0 := by positivity
      field_simp
    calc
      C (((d + 1).factorial : ℚ)⁻¹) * (C ((d + 1 : ℕ) : ℚ) * P ^ (d + 1 - 1) * dPs P)
        = (C (((d + 1).factorial : ℚ)⁻¹) * C ((d + 1 : ℕ) : ℚ)) * P ^ d * dPs P := by
            simp only [Nat.add_one_sub_one]; ring
      _ = C ((d.factorial : ℚ)⁻¹) * P ^ d * dPs P := by rw [hfac]
  have hderiv : dPs OMA.S_oeis_a049425.series =
      (1 + 2 * X + X ^ 2) * OMA.S_oeis_a049425.series := by
    ext k
    rw [coeff_dPs, hS_eq (k + 1) (k + 1) le_rfl, ← coeff_dPs, hdS k, hdparam, mul_comm,
      coeff_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (1 + 2 * X + X ^ 2) * coeff j (S k)) k,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (1 + 2 * X + X ^ 2) * coeff j OMA.S_oeis_a049425.series) k]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hS_eq (k - i) k (Nat.sub_le k i)]
  intro n
  have hcoeff := congrArg (coeff (n + 2)) hderiv
  rw [coeff_dPs] at hcoeff
  have hrhs : (1 + 2 * (X : PowerSeries ℚ) + X ^ 2) * OMA.S_oeis_a049425.series =
      OMA.S_oeis_a049425.series + 2 * (X * OMA.S_oeis_a049425.series) +
        X * (X * OMA.S_oeis_a049425.series) := by
    ring
  have hC2 : (2 : PowerSeries ℚ) = C (2 : ℚ) := by
    rw [← Nat.cast_ofNat, ← map_natCast C, Nat.cast_ofNat]
  rw [hrhs, map_add, map_add, hC2, coeff_C_mul, coeff_succ_X_mul,
    coeff_succ_X_mul, coeff_succ_X_mul] at hcoeff
  have hmul := congrArg (((n + 2).factorial : ℚ) * ·) hcoeff
  have hf (m : ℕ) : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have ha0 : OMA.S_oeis_a049425.a n = (n.factorial : ℚ) * coeff n OMA.S_oeis_a049425.series := rfl
  have ha1 : OMA.S_oeis_a049425.a (n + 1) =
      ((n + 1).factorial : ℚ) * coeff (n + 1) OMA.S_oeis_a049425.series := rfl
  have ha2 : OMA.S_oeis_a049425.a (n + 2) =
      ((n + 2).factorial : ℚ) * coeff (n + 2) OMA.S_oeis_a049425.series := rfl
  have ha3 : OMA.S_oeis_a049425.a (n + 3) =
      ((n + 3).factorial : ℚ) * coeff (n + 3) OMA.S_oeis_a049425.series := rfl
  rw [ha0, ha1, ha2, ha3, hf (n + 2), hf (n + 1), hf n]
  rw [hf (n + 1), hf n] at hmul
  push_cast at hmul ⊢
  linear_combination hmul
