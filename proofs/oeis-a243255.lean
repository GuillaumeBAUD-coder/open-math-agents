import OMAStatements.S_oeis_a243255

/-!
# Proof of the recurrence for OEIS A243255

The hypotheses make `T`, `U` algebraic over `ℚ(X)`: `T ^ 2 = 1 - 2 * X - 3 * X ^ 2`, `X * U ^ 2 = 2 * T + 3 * X - 2`; and `G` is given by `2 * G = 1 - U`.
The hypotheses on constant terms are not needed: the argument holds for every solution of these equations.

Write `θ = X d/dX`, so that the coefficient of `X ^ k` in `θ f` is `k` times that of `f`. The recurrence says that
the coefficient of `X ^ n` in `L G` vanishes for `n ≥ 4`, where `L = Σ_i X ^ i c_i(θ + i)` and `c_i(n)` is the
coefficient of `a(n - i)`. The proof shows that `L G` is a polynomial of degree less than 4:

* differentiating the equation of each algebraic series and multiplying by the inverse of the separant
  expresses its derivative in the basis of monomials in `T`, `U`, with a denominator in `ℚ[X]` (`n1_*`);
* `G` is put in that normal form (`n_0`), then `θ G`, `θ ^ 2 G` by differentiating the previous
  normal form and eliminating the derivatives of the algebraic series (`n_1`, ...);
* a combination of these normal forms gives `D * (L G - p) = 0` for a nonzero polynomial `D` in `X`
  and an explicit polynomial `p`, hence `L G = p`; the coefficient of `X ^ n` is the recurrence.

Here `p = 6 * X - 24 * X ^ 2` and `D = 512 * X ^ 4 - 7424 * X ^ 5 + 34592 * X ^ 6 - 39552 * X ^ 7 - 88128 * X ^ 8 + 120960 * X ^ 9 + 127008 * X ^ 10`.

Every step is an explicit polynomial identity checked by `linear_combination`.
-/

namespace OMA.S_oeis_a243255

open PowerSeries

/-- Numerals are constants for the derivative. -/
theorem d_ofNat (n : ℕ) [n.AtLeastTwo] : d⁄dX ℚ (ofNat(n) : ℚ⟦X⟧) = 0 := by
  first
    | exact Derivation.map_natCast (d⁄dX ℚ) n
    | (rw [← map_ofNat (C : ℚ →+* ℚ⟦X⟧) n]; exact derivative_C)

/-- The coefficient of `X ^ m` in `X * f'` is `m` times the coefficient of `X ^ m` in `f`. -/
theorem coeff_theta (f : ℚ⟦X⟧) (m : ℕ) : coeff m (X * d⁄dX ℚ f) = m * coeff m f := by
  cases m with
  | zero => simp
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

end OMA.S_oeis_a243255

set_option maxHeartbeats 3200000 in
open PowerSeries OMA.S_oeis_a243255 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243255.main := by
  intro T U G h1 _ h2 _ h3 _ n hn
  have hd1 : 2 * T * d⁄dX ℚ T =
      -2 - 6 * X := by
    have e1 : d⁄dX ℚ (T ^ 2 : ℚ⟦X⟧) =
        2 * T * d⁄dX ℚ T := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ (1 - 2 * X - 3 * X ^ 2 : ℚ⟦X⟧) =
        -2 - 6 * X := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) h1).trans e2)
  have n1_1 : -(2 - 4 * X - 6 * X ^ 2) * d⁄dX ℚ T =
      (2 + 6 * X) * T := by
    linear_combination -T * hd1 + (2 * d⁄dX ℚ T) * h1
  have hd2 : U ^ 2 + 2 * X * U * d⁄dX ℚ U =
      3 + 2 * d⁄dX ℚ T := by
    have e1 : d⁄dX ℚ (X * U ^ 2 : ℚ⟦X⟧) =
        U ^ 2 + 2 * X * U * d⁄dX ℚ U := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ (2 * T + 3 * X - 2 : ℚ⟦X⟧) =
        3 + 2 * d⁄dX ℚ T := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) h2).trans e2)
  have n1_2 : (16 * X ^ 2 - 116 * X ^ 3 + 120 * X ^ 4 + 252 * X ^ 5) * d⁄dX ℚ U =
      -(4 * X - 8 * X ^ 2 - 12 * X ^ 3) * U + (4 * X - 36 * X ^ 2) * T * U := by
    linear_combination ((4 * X - 14 * X ^ 2 + 18 * X ^ 4) * U + (4 * X - 8 * X ^ 2 - 12 * X ^ 3) * T * U) * hd2
      + (-(8 - 8 * X) * U - (16 * X - 32 * X ^ 2 - 48 * X ^ 3) * d⁄dX ℚ U) * h1
      + (-(4 - 14 * X + 18 * X ^ 3) * U - (8 * X - 28 * X ^ 2 + 36 * X ^ 4) * d⁄dX ℚ U - (4 - 8 * X - 12 * X ^ 2) * T * U - (8 * X - 16 * X ^ 2 - 24 * X ^ 3) * T * d⁄dX ℚ U) * h2
      + (-(4 * X - 6 * X ^ 2) * U - 4 * X * T * U) * n1_1
  have n_0 : 2 * G =
      1 - U := by
    linear_combination h3
  obtain ⟨Θ1, hΘ1, hc1⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ G ∧ ∀ k, coeff k Θ = k * coeff k G :=
    ⟨_, rfl, coeff_theta G⟩
  have hdn_0 : 2 * d⁄dX ℚ G =
      -d⁄dX ℚ U := by
    have e1 : d⁄dX ℚ (2 * G : ℚ⟦X⟧) =
        2 * d⁄dX ℚ G := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ (1 - U : ℚ⟦X⟧) =
        -d⁄dX ℚ U := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) n_0).trans e2)
  have n_1 : (32 * X ^ 2 - 232 * X ^ 3 + 240 * X ^ 4 + 504 * X ^ 5) * Θ1 =
      (4 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4) * U - (4 * X ^ 2 - 36 * X ^ 3) * T * U := by
    rw [hΘ1]
    linear_combination (16 * X ^ 3 - 116 * X ^ 4 + 120 * X ^ 5 + 252 * X ^ 6) * hdn_0 - X * n1_2
  obtain ⟨Θ2, hΘ2, hc2⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ Θ1 ∧ ∀ k, coeff k Θ = k * coeff k Θ1 :=
    ⟨_, rfl, coeff_theta Θ1⟩
  have hdn_1 : (64 * X - 696 * X ^ 2 + 960 * X ^ 3 + 2520 * X ^ 4) * Θ1 + (32 * X ^ 2 - 232 * X ^ 3 + 240 * X ^ 4 + 504 * X ^ 5) * d⁄dX ℚ Θ1 =
      (8 * X - 24 * X ^ 2 - 48 * X ^ 3) * U + (4 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4) * d⁄dX ℚ U
      - (8 * X - 108 * X ^ 2) * T * U - (4 * X ^ 2 - 36 * X ^ 3) * U * d⁄dX ℚ T
      - (4 * X ^ 2 - 36 * X ^ 3) * T * d⁄dX ℚ U := by
    have e1 : d⁄dX ℚ ((32 * X ^ 2 - 232 * X ^ 3 + 240 * X ^ 4 + 504 * X ^ 5) * Θ1 : ℚ⟦X⟧) =
        (64 * X - 696 * X ^ 2 + 960 * X ^ 3 + 2520 * X ^ 4) * Θ1 + (32 * X ^ 2 - 232 * X ^ 3 + 240 * X ^ 4 + 504 * X ^ 5) * d⁄dX ℚ Θ1 := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ ((4 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4) * U - (4 * X ^ 2 - 36 * X ^ 3) * T * U : ℚ⟦X⟧) =
        (8 * X - 24 * X ^ 2 - 48 * X ^ 3) * U + (4 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4) * d⁄dX ℚ U
        - (8 * X - 108 * X ^ 2) * T * U - (4 * X ^ 2 - 36 * X ^ 3) * U * d⁄dX ℚ T
        - (4 * X ^ 2 - 36 * X ^ 3) * T * d⁄dX ℚ U := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) n_1).trans e2)
  have n_2 : (512 * X ^ 4 - 7424 * X ^ 5 + 34592 * X ^ 6 - 39552 * X ^ 7 - 88128 * X ^ 8 + 120960 * X ^ 9 + 127008 * X ^ 10) * Θ2 =
      -(32 * X ^ 4 - 720 * X ^ 5 + 3136 * X ^ 6 - 864 * X ^ 7 - 7776 * X ^ 8 - 3024 * X ^ 9) * U
      + (32 * X ^ 4 - 176 * X ^ 5 + 720 * X ^ 6 - 144 * X ^ 7 - 9072 * X ^ 8) * T * U := by
    rw [hΘ2]
    linear_combination (16 * X ^ 3 - 116 * X ^ 4 + 120 * X ^ 5 + 252 * X ^ 6) * hdn_1
      + ((32 * X ^ 5 - 456 * X ^ 6 + 1512 * X ^ 7) * U) * n1_1 + (4 * X ^ 3 - 8 * X ^ 4 - 12 * X ^ 5 - (4 * X ^ 3 - 36 * X ^ 4) * T) * n1_2
      + (-32 * X ^ 2 + 348 * X ^ 3 - 480 * X ^ 4 - 1260 * X ^ 5) * n_1
      + (-(16 * X ^ 4 - 288 * X ^ 5 + 1296 * X ^ 6) * U) * h1
  have keyD : (512 * X ^ 4 - 7424 * X ^ 5 + 34592 * X ^ 6 - 39552 * X ^ 7 - 88128 * X ^ 8 + 120960 * X ^ 9 + 127008 * X ^ 10) * (-6 * X + 24 * X ^ 2 + (12 * X - 48 * X ^ 2) * G + (2 - 11 * X + 45 * X ^ 2 - 9 * X ^ 3 - 567 * X ^ 4) * Θ1
      + (4 - 65 * X + 291 * X ^ 2 - 207 * X ^ 3 - 567 * X ^ 4) * Θ2) = 0 := by
    linear_combination (3072 * X ^ 5 - 56832 * X ^ 6 + 385728 * X ^ 7 - 1067520 * X ^ 8 + 420480 * X ^ 9 + 2840832 * X ^ 10 - 2140992 * X ^ 11 - 3048192 * X ^ 12) * n_0
      + (32 * X ^ 2 - 408 * X ^ 3 + 2236 * X ^ 4 - 6180 * X ^ 5 - 5400 * X ^ 6 + 76032 * X ^ 7 - 70308 * X ^ 8 - 142884 * X ^ 9) * n_1
      + (4 - 65 * X + 291 * X ^ 2 - 207 * X ^ 3 - 567 * X ^ 4) * n_2
  have hF : (512 - 7424 * X + 34592 * X ^ 2 - 39552 * X ^ 3 - 88128 * X ^ 4 + 120960 * X ^ 5 + 127008 * X ^ 6 : ℚ⟦X⟧) ≠ 0 := by
    have hrw : (512 - 7424 * X + 34592 * X ^ 2 - 39552 * X ^ 3 - 88128 * X ^ 4 + 120960 * X ^ 5 + 127008 * X ^ 6 : ℚ⟦X⟧) = C (512) + X * (-7424 + 34592 * X - 39552 * X ^ 2 - 88128 * X ^ 3 + 120960 * X ^ 4 + 127008 * X ^ 5) := by
      simp only [map_ofNat, map_neg, map_one]
      ring
    rw [hrw]
    intro h
    have h0 := congrArg (coeff 0) h
    first
      | (simp only [map_add, coeff_zero_C, coeff_zero_X_mul, map_zero, add_zero] at h0; norm_num at h0)
      | (simp only [map_add, coeff_zero_C, coeff_zero_X_mul, map_zero, add_zero] at h0)
  have hD : (512 * X ^ 4 - 7424 * X ^ 5 + 34592 * X ^ 6 - 39552 * X ^ 7 - 88128 * X ^ 8 + 120960 * X ^ 9 + 127008 * X ^ 10 : ℚ⟦X⟧) ≠ 0 := by
    have hrw : (512 * X ^ 4 - 7424 * X ^ 5 + 34592 * X ^ 6 - 39552 * X ^ 7 - 88128 * X ^ 8 + 120960 * X ^ 9 + 127008 * X ^ 10 : ℚ⟦X⟧) = X ^ 4 * (512 - 7424 * X + 34592 * X ^ 2 - 39552 * X ^ 3 - 88128 * X ^ 4 + 120960 * X ^ 5 + 127008 * X ^ 6) := by ring
    rw [hrw]
    exact mul_ne_zero (pow_ne_zero 4 X_ne_zero) hF
  have ode : -6 * X + 24 * X ^ 2 + (12 * X - 48 * X ^ 2) * G + (2 - 11 * X + 45 * X ^ 2 - 9 * X ^ 3 - 567 * X ^ 4) * Θ1
      + (4 - 65 * X + 291 * X ^ 2 - 207 * X ^ 3 - 567 * X ^ 4) * Θ2 = 0 :=
    (mul_eq_zero.mp keyD).resolve_left (hD)
  have key : C (12) * (X * G)
      + C (-48) * (X * (X * G))
      + C (2) * Θ1
      + C (-11) * (X * Θ1)
      + C (45) * (X * (X * Θ1))
      + C (-9) * (X * (X * (X * Θ1)))
      + C (-567) * (X * (X * (X * (X * Θ1))))
      + C (4) * Θ2
      + C (-65) * (X * Θ2)
      + C (291) * (X * (X * Θ2))
      + C (-207) * (X * (X * (X * Θ2)))
      + C (-567) * (X * (X * (X * (X * Θ2))))
      + C (-6) * (X * 1)
      + C (24) * (X * (X * 1)) = 0 := by
    simp only [map_ofNat, map_neg, map_one]
    linear_combination ode
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have hne2 : m + 1 + 1 ≠ 0 := by omega
  have hne3 : m + 1 + 1 + 1 ≠ 0 := by omega
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) key
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, hc2, hc1, map_zero, coeff_one, if_neg hne2, if_neg hne3] at h
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := by omega
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := by omega
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := by omega
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := by omega
  rw [e1, e2, e3, e4]
  push_cast at h ⊢
  linear_combination h
