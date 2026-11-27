import OMAStatements.S_oeis_a108629

-- Problem: A108629: Expansion of g.f.: (1+x - sqrt(1-2*x-3*x^2-4*x^3))/(2+2*x+2*x^2).
-- Upstream: formal-conjectures statements/oeis-a108629.lean:0 (declaration OMA.S_oeis_a108629.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a108629

open OMA.S_oeis_a108629
open PowerSeries

private lemma hasSubst_radicandTail : PowerSeries.HasSubst radicandTail := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  simp [radicandTail]

private lemma rootSeries_sq :
    rootSeries * rootSeries = 1 - 2 * X - 3 * X ^ 2 - 4 * X ^ 3 := by
  unfold rootSeries
  have hs := hasSubst_radicandTail
  rw [← PowerSeries.subst_mul hs, ← PowerSeries.binomialSeries_add]
  have hhalf : (1 / 2 : ℚ) + (1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
  rw [hhalf, PowerSeries.binomialSeries_nat, pow_one, PowerSeries.subst_add hs,
    PowerSeries.subst_X hs]
  have hone : PowerSeries.subst radicandTail (1 : PowerSeries ℚ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hs, map_one]
  rw [hone]
  unfold radicandTail
  ring

private lemma deriv_X : derivative ℚ (X : PowerSeries ℚ) = 1 := by
  ext n
  rw [PowerSeries.coeff_derivative]
  cases n with
  | zero => simp
  | succ m =>
    simp [PowerSeries.coeff_X]

private lemma deriv_X_pow (k : ℕ) :
    derivative ℚ ((X : PowerSeries ℚ) ^ (k + 1)) = ((k + 1 : ℕ) : PowerSeries ℚ) * X ^ k := by
  rw [Derivation.leibniz_pow, deriv_X, smul_eq_mul, mul_one, nsmul_eq_mul, Nat.add_sub_cancel]

private lemma deriv_mul_eq (f g : PowerSeries ℚ) :
    derivative ℚ (f * g) = f * derivative ℚ g + g * derivative ℚ f := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

private lemma deriv_C_mul (c : ℚ) (f : PowerSeries ℚ) :
    derivative ℚ (C c * f) = C c * derivative ℚ f := by
  rw [deriv_mul_eq]
  have hc : derivative ℚ (C c) = 0 := by
    ext n
    rw [PowerSeries.coeff_derivative]
    simp
  rw [hc, mul_zero, add_zero]

private lemma deriv_ofNat_mul (k : ℕ) (f : PowerSeries ℚ) :
    derivative ℚ ((k : PowerSeries ℚ) * f) = (k : PowerSeries ℚ) * derivative ℚ f := by
  have hk : (k : PowerSeries ℚ) = C (k : ℚ) := (map_natCast C k).symm
  rw [hk, deriv_C_mul]

private lemma deriv_rootSeries_ode :
    2 * (1 - 2 * X - 3 * X ^ 2 - 4 * X ^ 3) * derivative ℚ rootSeries =
      (-2 - 6 * X - 12 * X ^ 2) * rootSeries := by
  have hd := congrArg (derivative ℚ) rootSeries_sq
  have hlhs : derivative ℚ (rootSeries * rootSeries) = 2 * rootSeries * derivative ℚ rootSeries := by
    rw [deriv_mul_eq]
    ring
  have hrhs : derivative ℚ (1 - 2 * X - 3 * X ^ 2 - 4 * X ^ 3 : PowerSeries ℚ) =
      -2 - 6 * X - 12 * X ^ 2 := by
    have h1 : derivative ℚ (1 : PowerSeries ℚ) = 0 := by
      ext n; rw [PowerSeries.coeff_derivative]; simp
    have h2 : derivative ℚ ((2 : PowerSeries ℚ) * X) = 2 := by
      rw [← map_ofNat C 2, deriv_C_mul, deriv_X, mul_one, map_ofNat]
    have h3 : derivative ℚ ((3 : PowerSeries ℚ) * X ^ 2) = 6 * X := by
      rw [← map_ofNat C 3, deriv_C_mul, deriv_X_pow 1, map_ofNat]
      push_cast
      ring
    have h4 : derivative ℚ ((4 : PowerSeries ℚ) * X ^ 3) = 12 * X ^ 2 := by
      rw [← map_ofNat C 4, deriv_C_mul, deriv_X_pow 2, map_ofNat]
      push_cast
      ring
    simp only [map_sub, h1, h2, h3, h4]
    ring
  rw [hlhs, hrhs] at hd
  calc
    2 * (1 - 2 * X - 3 * X ^ 2 - 4 * X ^ 3) * derivative ℚ rootSeries
        = 2 * (rootSeries * rootSeries) * derivative ℚ rootSeries := by rw [rootSeries_sq]
    _ = (2 * rootSeries * derivative ℚ rootSeries) * rootSeries := by ring
    _ = (-2 - 6 * X - 12 * X ^ 2) * rootSeries := by rw [hd]

private lemma rootSeries_eq_series :
    rootSeries = 1 + X - 2 * (1 + X + X ^ 2) * series := by
  have hq0 : constantCoeff (2 * (1 + X + X ^ 2) : PowerSeries ℚ) ≠ 0 := by
    simp only [map_mul, map_add, map_one, map_pow, constantCoeff_X, map_ofNat]
    norm_num
  have hmul : series * (2 * (1 + X + X ^ 2)) = 1 + X - rootSeries := by
    unfold series
    rw [mul_assoc, mul_comm (2 * (1 + X + X ^ 2))⁻¹, PowerSeries.mul_inv_cancel _ hq0, mul_one]
  linear_combination hmul

private lemma deriv_rootSeries_eq_series :
    derivative ℚ rootSeries =
      1 - 2 * (1 + 2 * X) * series - 2 * (1 + X + X ^ 2) * derivative ℚ series := by
  rw [rootSeries_eq_series]
  have h1 : derivative ℚ (1 : PowerSeries ℚ) = 0 := by
    ext n; rw [PowerSeries.coeff_derivative]; simp
  have hq : derivative ℚ (2 * (1 + X + X ^ 2) : PowerSeries ℚ) = 2 * (1 + 2 * X) := by
    rw [← map_ofNat C 2, deriv_C_mul, map_add, map_add, h1, deriv_X, deriv_X_pow 1, map_ofNat]
    push_cast
    ring
  rw [map_sub, map_add, h1, deriv_X, deriv_mul_eq, hq]
  ring

private lemma series_ode :
    4 * (1 - X - 4 * X ^ 2 - 9 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 5) * derivative ℚ series +
      4 * (2 + 4 * X + 3 * X ^ 2 - X ^ 3 - 2 * X ^ 4) * series =
      4 * (1 + X + 3 * X ^ 2 + X ^ 3) := by
  have h := deriv_rootSeries_ode
  rw [deriv_rootSeries_eq_series, rootSeries_eq_series] at h
  linear_combination -h

private lemma coeff_C_mul_X_pow_mul (c : ℚ) (k m : ℕ) (hk : k ≤ m) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (C c * (X ^ k * f)) = c * PowerSeries.coeff (m - k) f := by
  rw [PowerSeries.coeff_C_mul, mul_comm (X ^ k) f, PowerSeries.coeff_mul_X_pow', if_pos hk]

private lemma coeff_X_pow_mul (k m : ℕ) (hk : k ≤ m) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (X ^ k * f) = PowerSeries.coeff (m - k) f := by
  rw [mul_comm (X ^ k) f, PowerSeries.coeff_mul_X_pow', if_pos hk]

private lemma coeff_C_mul_X_pow_of_lt (c : ℚ) (k m : ℕ) (hk : k < m) :
    PowerSeries.coeff m (C c * (X : PowerSeries ℚ) ^ k) = 0 := by
  rw [PowerSeries.coeff_C_mul_X_pow, if_neg (by omega)]

private lemma main_proof : ∀ n : ℕ, 6 ≤ n →
    (n : ℚ) * a n =
      ((n : ℚ) - 3) * a (n - 1) + 4 * ((n : ℚ) - 3) * a (n - 2) +
      3 * (3 * (n : ℚ) - 10) * a (n - 3) + (7 * (n : ℚ) - 27) * a (n - 4) +
      2 * (2 * (n : ℚ) - 9) * a (n - 5) := by
  intro n hn
  set m := n - 1 with hm_def
  have hm5 : 5 ≤ m := by omega
  have hode := congrArg (PowerSeries.coeff m) series_ode
  have h4 : (4 : PowerSeries ℚ) = C (4 : ℚ) := (map_ofNat C 4).symm
  have hL :
      4 * (1 - X - 4 * X ^ 2 - 9 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 5) * derivative ℚ series +
        4 * (2 + 4 * X + 3 * X ^ 2 - X ^ 3 - 2 * X ^ 4) * series =
        C (4 : ℚ) * derivative ℚ series
        - C (4 : ℚ) * (X ^ 1 * derivative ℚ series)
        - C (16 : ℚ) * (X ^ 2 * derivative ℚ series)
        - C (36 : ℚ) * (X ^ 3 * derivative ℚ series)
        - C (28 : ℚ) * (X ^ 4 * derivative ℚ series)
        - C (16 : ℚ) * (X ^ 5 * derivative ℚ series)
        + C (8 : ℚ) * series
        + C (16 : ℚ) * (X ^ 1 * series)
        + C (12 : ℚ) * (X ^ 2 * series)
        - C (4 : ℚ) * (X ^ 3 * series)
        - C (8 : ℚ) * (X ^ 4 * series) := by
    have h8 : C (8 : ℚ) = (8 : PowerSeries ℚ) := map_ofNat C 8
    have h12 : C (12 : ℚ) = (12 : PowerSeries ℚ) := map_ofNat C 12
    have h16 : C (16 : ℚ) = (16 : PowerSeries ℚ) := map_ofNat C 16
    have h28 : C (28 : ℚ) = (28 : PowerSeries ℚ) := map_ofNat C 28
    have h36 : C (36 : ℚ) = (36 : PowerSeries ℚ) := map_ofNat C 36
    rw [← h4, h8, h12, h16, h28, h36, pow_one]
    ring
  have hR : (4 * (1 + X + 3 * X ^ 2 + X ^ 3) : PowerSeries ℚ) =
      C (4 : ℚ) * X ^ 0 + C (4 : ℚ) * X ^ 1 + C (12 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 := by
    have h12 : C (12 : ℚ) = (12 : PowerSeries ℚ) := map_ofNat C 12
    rw [← h4, h12, pow_zero, pow_one]
    ring
  rw [hL, hR] at hode
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    coeff_C_mul_X_pow_mul _ 1 m (by omega),
    coeff_C_mul_X_pow_mul _ 2 m (by omega),
    coeff_C_mul_X_pow_mul _ 3 m (by omega),
    coeff_C_mul_X_pow_mul _ 4 m (by omega),
    coeff_C_mul_X_pow_mul _ 5 m (by omega),
    coeff_C_mul_X_pow_of_lt _ 0 m (by omega),
    coeff_C_mul_X_pow_of_lt _ 1 m (by omega),
    coeff_C_mul_X_pow_of_lt _ 2 m (by omega),
    coeff_C_mul_X_pow_of_lt _ 3 m (by omega),
    PowerSeries.coeff_derivative] at hode
  change
    4 * (a (m + 1) * ((m : ℚ) + 1))
    - 4 * (a ((m - 1) + 1) * (((m - 1 : ℕ) : ℚ) + 1))
    - 16 * (a ((m - 2) + 1) * (((m - 2 : ℕ) : ℚ) + 1))
    - 36 * (a ((m - 3) + 1) * (((m - 3 : ℕ) : ℚ) + 1))
    - 28 * (a ((m - 4) + 1) * (((m - 4 : ℕ) : ℚ) + 1))
    - 16 * (a ((m - 5) + 1) * (((m - 5 : ℕ) : ℚ) + 1))
    + 8 * a m
    + 16 * a (m - 1)
    + 12 * a (m - 2)
    - 4 * a (m - 3)
    - 8 * a (m - 4) = 0 + 0 + 0 + 0 at hode
  have hm0 : m + 1 = n := by omega
  have hm1 : (m - 1) + 1 = n - 1 := by omega
  have hm2 : (m - 2) + 1 = n - 2 := by omega
  have hm3 : (m - 3) + 1 = n - 3 := by omega
  have hm4 : (m - 4) + 1 = n - 4 := by omega
  have hm5' : (m - 5) + 1 = n - 5 := by omega
  have hk0 : m = n - 1 := by omega
  have hk1 : m - 1 = n - 2 := by omega
  have hk2 : m - 2 = n - 3 := by omega
  have hk3 : m - 3 = n - 4 := by omega
  have hk4 : m - 4 = n - 5 := by omega
  have hk5 : m - 5 = n - 6 := by omega
  rw [hm0, hm1, hm2, hm3, hm4, hm5', hk0, hk1, hk2, hk3, hk4, hk5] at hode
  have hc1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hc2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
  have hc3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by rw [Nat.cast_sub (by omega)]; simp
  have hc4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by rw [Nat.cast_sub (by omega)]; simp
  have hc5 : ((n - 5 : ℕ) : ℚ) = (n : ℚ) - 5 := by rw [Nat.cast_sub (by omega)]; simp
  have hc6 : ((n - 6 : ℕ) : ℚ) = (n : ℚ) - 6 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hc1, hc2, hc3, hc4, hc5, hc6] at hode
  linarith

end OMA.Proof_oeis_a108629

theorem OMA.solution : type_of% @OMA.S_oeis_a108629.main :=
  OMA.Proof_oeis_a108629.main_proof
