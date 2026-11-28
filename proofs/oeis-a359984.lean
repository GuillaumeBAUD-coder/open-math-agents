import OMAStatements.S_oeis_a359984

/-!
# Proof of the recurrence for OEIS A359984

The hypotheses make `T` algebraic over `ℚ(X)`: `T = 1 + (4 * X + X ^ 2) * T ^ 2 - 3 * X ^ 2 * (1 + X) * T ^ 3`; and `G` is given by `G = 1 + X ^ 2 * T ^ 2 - 3 * X ^ 3 * T ^ 3`.

Write `θ = X d/dX`, so that the coefficient of `X ^ k` in `θ f` is `k` times that of `f`. The recurrence says that
the coefficient of `X ^ n` in `L G` vanishes for `n ≥ 7`, where `L = Σ_i X ^ i c_i(θ + i)` and `c_i(n)` is the
coefficient of `a(n - i)`. The proof shows that `L G` is a polynomial of degree less than 7:

* differentiating the equation of each algebraic series and multiplying by the inverse of the separant
  expresses its derivative in the basis of monomials in `T`, with a denominator in `ℚ[X]` (`n1_*`);
* `G` is put in that normal form (`n_0`), then `θ G`, `θ ^ 2 G` by differentiating the previous
  normal form and eliminating the derivatives of the algebraic series (`n_1`, ...);
* a combination of these normal forms gives `D * (L G - p) = 0` for a nonzero polynomial `D` in `X`
  and an explicit polynomial `p`, hence `L G = p`; the coefficient of `X ^ n` is the recurrence.

Here `p = 160 * X ^ 2 + 500 * X ^ 3 - 26336 * X ^ 4` and `D = 16 * X ^ 2 - 304 * X ^ 3 - 384 * X ^ 4 + 11424 * X ^ 5 + 100456 * X ^ 6 + 413056 * X ^ 7 + 1061016 * X ^ 8 + 1776056 * X ^ 9 + 1885793 * X ^ 10 + 1205803 * X ^ 11 + 420147 * X ^ 12 + 61009 * X ^ 13`.

Every step is an explicit polynomial identity checked by `linear_combination`.
-/

namespace OMA.S_oeis_a359984

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

end OMA.S_oeis_a359984

set_option maxHeartbeats 3200000 in
open PowerSeries OMA.S_oeis_a359984 in
theorem OMA.solution : type_of% @OMA.S_oeis_a359984.main := by
  intro T G h1 h2 n hn
  have hd1 : d⁄dX ℚ T =
      (4 + 2 * X) * T ^ 2 + (8 * X + 2 * X ^ 2) * T * d⁄dX ℚ T - (6 * X + 9 * X ^ 2) * T ^ 3
      - (9 * X ^ 2 + 9 * X ^ 3) * T ^ 2 * d⁄dX ℚ T := by
    have e1 : d⁄dX ℚ (T : ℚ⟦X⟧) =
        d⁄dX ℚ T := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ (1 + (4 * X + X ^ 2) * T ^ 2 - 3 * X ^ 2 * (1 + X) * T ^ 3 : ℚ⟦X⟧) =
        (4 + 2 * X) * T ^ 2 + (8 * X + 2 * X ^ 2) * T * d⁄dX ℚ T - (6 * X + 9 * X ^ 2) * T ^ 3
        - (9 * X ^ 2 + 9 * X ^ 3) * T ^ 2 * d⁄dX ℚ T := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) h1).trans e2)
  have n1_1 : -(4 * X - 44 * X ^ 2 - 164 * X ^ 3 - 480 * X ^ 4 - 247 * X ^ 5) * d⁄dX ℚ T =
      -4 - 30 * X - 92 * X ^ 2 + (4 - 2 * X - 48 * X ^ 2 - 400 * X ^ 3 - 247 * X ^ 4) * T
      - (36 * X ^ 2 + 132 * X ^ 3 - 21 * X ^ 4) * T ^ 2 := by
    linear_combination (-4 * X - 32 * X ^ 2 - 46 * X ^ 3 - 9 * X ^ 4 + (44 * X ^ 2 + 72 * X ^ 3 + 165 * X ^ 4 + 83 * X ^ 5) * T - (42 * X ^ 3 + 36 * X ^ 4 + 6 * X ^ 6) * T ^ 2) * hd1
      + (-4 - 30 * X - 92 * X ^ 2 - (32 * X + 140 * X ^ 2 + 400 * X ^ 3 + 247 * X ^ 4) * T - (76 * X ^ 2 + 210 * X ^ 3 + 489 * X ^ 4 + 247 * X ^ 5) * d⁄dX ℚ T + (84 * X ^ 2 + 114 * X ^ 3 - 6 * X ^ 4 + 18 * X ^ 5) * T ^ 2 + (126 * X ^ 3 + 108 * X ^ 4 + 18 * X ^ 6) * T * d⁄dX ℚ T) * h1
  have n_0 : (1 + X) * G =
      1 + X * T - 3 * X ^ 2 * T ^ 2 := by
    linear_combination (1 + X) * h2 - X * h1
  obtain ⟨Θ1, hΘ1, hc1⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ G ∧ ∀ k, coeff k Θ = k * coeff k G :=
    ⟨_, rfl, coeff_theta G⟩
  have hdn_0 : G + (1 + X) * d⁄dX ℚ G =
      T + X * d⁄dX ℚ T - 6 * X * T ^ 2 - 6 * X ^ 2 * T * d⁄dX ℚ T := by
    have e1 : d⁄dX ℚ ((1 + X) * G : ℚ⟦X⟧) =
        G + (1 + X) * d⁄dX ℚ G := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ (1 + X * T - 3 * X ^ 2 * T ^ 2 : ℚ⟦X⟧) =
        T + X * d⁄dX ℚ T - 6 * X * T ^ 2 - 6 * X ^ 2 * T * d⁄dX ℚ T := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) n_0).trans e2)
  have n_1 : -(4 * X - 36 * X ^ 2 - 248 * X ^ 3 - 852 * X ^ 4 - 1371 * X ^ 5 - 974 * X ^ 6 - 247 * X ^ 7) * Θ1 =
      -6 * X ^ 3 - 22 * X ^ 4 - 614 * X ^ 5 - 247 * X ^ 6 - (2 * X ^ 3 - 54 * X ^ 4 - 806 * X ^ 5 - 152 * X ^ 6 + 247 * X ^ 7) * T
      - (12 * X ^ 4 - 144 * X ^ 5 + 699 * X ^ 6 - 939 * X ^ 7 - 741 * X ^ 8) * T ^ 2 := by
    rw [hΘ1]
    linear_combination (-4 * X ^ 2 + 40 * X ^ 3 + 208 * X ^ 4 + 644 * X ^ 5 + 727 * X ^ 6 + 247 * X ^ 7) * hdn_0
      + (X ^ 2 + X ^ 3 - (6 * X ^ 3 + 6 * X ^ 4) * T) * n1_1 + (4 * X ^ 2 - 44 * X ^ 3 - 164 * X ^ 4 - 480 * X ^ 5 - 247 * X ^ 6) * n_0
      + (72 * X ^ 3 + 264 * X ^ 4 - 42 * X ^ 5) * h1
  obtain ⟨Θ2, hΘ2, hc2⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ Θ1 ∧ ∀ k, coeff k Θ = k * coeff k Θ1 :=
    ⟨_, rfl, coeff_theta Θ1⟩
  have hdn_1 : -(4 - 72 * X - 744 * X ^ 2 - 3408 * X ^ 3 - 6855 * X ^ 4 - 5844 * X ^ 5 - 1729 * X ^ 6) * Θ1
      - (4 * X - 36 * X ^ 2 - 248 * X ^ 3 - 852 * X ^ 4 - 1371 * X ^ 5 - 974 * X ^ 6 - 247 * X ^ 7) * d⁄dX ℚ Θ1 =
      -18 * X ^ 2 - 88 * X ^ 3 - 3070 * X ^ 4 - 1482 * X ^ 5 - (6 * X ^ 2 - 216 * X ^ 3 - 4030 * X ^ 4 - 912 * X ^ 5 + 1729 * X ^ 6) * T
      - (2 * X ^ 3 - 54 * X ^ 4 - 806 * X ^ 5 - 152 * X ^ 6 + 247 * X ^ 7) * d⁄dX ℚ T
      - (48 * X ^ 3 - 720 * X ^ 4 + 4194 * X ^ 5 - 6573 * X ^ 6 - 5928 * X ^ 7) * T ^ 2
      - (24 * X ^ 4 - 288 * X ^ 5 + 1398 * X ^ 6 - 1878 * X ^ 7 - 1482 * X ^ 8) * T * d⁄dX ℚ T := by
    have e1 : d⁄dX ℚ (-(4 * X - 36 * X ^ 2 - 248 * X ^ 3 - 852 * X ^ 4 - 1371 * X ^ 5 - 974 * X ^ 6 - 247 * X ^ 7) * Θ1 : ℚ⟦X⟧) =
        -(4 - 72 * X - 744 * X ^ 2 - 3408 * X ^ 3 - 6855 * X ^ 4 - 5844 * X ^ 5 - 1729 * X ^ 6) * Θ1
        - (4 * X - 36 * X ^ 2 - 248 * X ^ 3 - 852 * X ^ 4 - 1371 * X ^ 5 - 974 * X ^ 6 - 247 * X ^ 7) * d⁄dX ℚ Θ1 := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ (-6 * X ^ 3 - 22 * X ^ 4 - 614 * X ^ 5 - 247 * X ^ 6 - (2 * X ^ 3 - 54 * X ^ 4 - 806 * X ^ 5 - 152 * X ^ 6 + 247 * X ^ 7) * T
        - (12 * X ^ 4 - 144 * X ^ 5 + 699 * X ^ 6 - 939 * X ^ 7 - 741 * X ^ 8) * T ^ 2 : ℚ⟦X⟧) =
        -18 * X ^ 2 - 88 * X ^ 3 - 3070 * X ^ 4 - 1482 * X ^ 5 - (6 * X ^ 2 - 216 * X ^ 3 - 4030 * X ^ 4 - 912 * X ^ 5 + 1729 * X ^ 6) * T
        - (2 * X ^ 3 - 54 * X ^ 4 - 806 * X ^ 5 - 152 * X ^ 6 + 247 * X ^ 7) * d⁄dX ℚ T
        - (48 * X ^ 3 - 720 * X ^ 4 + 4194 * X ^ 5 - 6573 * X ^ 6 - 5928 * X ^ 7) * T ^ 2
        - (24 * X ^ 4 - 288 * X ^ 5 + 1398 * X ^ 6 - 1878 * X ^ 7 - 1482 * X ^ 8) * T * d⁄dX ℚ T := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) n_1).trans e2)
  have n_2 : (16 * X ^ 2 - 304 * X ^ 3 - 384 * X ^ 4 + 11424 * X ^ 5 + 100456 * X ^ 6 + 413056 * X ^ 7 + 1061016 * X ^ 8 + 1776056 * X ^ 9 + 1885793 * X ^ 10 + 1205803 * X ^ 11 + 420147 * X ^ 12 + 61009 * X ^ 13) * Θ2 =
      56 * X ^ 4 + 140 * X ^ 5 + 1024 * X ^ 6 - 100436 * X ^ 7 - 320192 * X ^ 8
      - 599998 * X ^ 9 - 2518 * X ^ 10 + 275405 * X ^ 11 + 61009 * X ^ 12
      + (8 * X ^ 4 - 716 * X ^ 5 - 2776 * X ^ 6 + 102584 * X ^ 7 + 227918 * X ^ 8 + 142306 * X ^ 9 - 1140074 * X ^ 10 - 1348040 * X ^ 11 - 292201 * X ^ 12 + 61009 * X ^ 13) * T
      + (48 * X ^ 5 - 984 * X ^ 6 + 15132 * X ^ 7 - 105090 * X ^ 8 - 163932 * X ^ 9 - 75000 * X ^ 10 + 1795425 * X ^ 11 + 1360878 * X ^ 12 - 157092 * X ^ 13 - 183027 * X ^ 14) * T ^ 2 := by
    rw [hΘ2]
    linear_combination (-4 * X ^ 2 + 40 * X ^ 3 + 208 * X ^ 4 + 644 * X ^ 5 + 727 * X ^ 6 + 247 * X ^ 7) * hdn_1
      + (-2 * X ^ 4 + 52 * X ^ 5 + 860 * X ^ 6 + 958 * X ^ 7 - 95 * X ^ 8 - 247 * X ^ 9 - (24 * X ^ 5 - 264 * X ^ 6 + 1110 * X ^ 7 - 480 * X ^ 8 - 3360 * X ^ 9 - 1482 * X ^ 10) * T) * n1_1
      + (4 * X - 76 * X ^ 2 - 668 * X ^ 3 - 2740 * X ^ 4 - 4115 * X ^ 5 - 1729 * X ^ 6) * n_1
      + (288 * X ^ 5 - 2400 * X ^ 6 + 3936 * X ^ 7 + 40992 * X ^ 8 - 110202 * X ^ 9 - 52062 * X ^ 10 + 10374 * X ^ 11) * h1
  have keyD : (16 * X ^ 2 - 304 * X ^ 3 - 384 * X ^ 4 + 11424 * X ^ 5 + 100456 * X ^ 6 + 413056 * X ^ 7 + 1061016 * X ^ 8 + 1776056 * X ^ 9 + 1885793 * X ^ 10 + 1205803 * X ^ 11 + 420147 * X ^ 12 + 61009 * X ^ 13) * (-160 * X ^ 2 - 500 * X ^ 3 + 26336 * X ^ 4 + (144 * X ^ 2 + 444 * X ^ 3 - 24972 * X ^ 4 + 17428 * X ^ 5 + 61706 * X ^ 6 + 76570 * X ^ 7) * G
      - (8 - 356 * X + 1112 * X ^ 2 + 21406 * X ^ 3 + 36352 * X ^ 4 + 2750 * X ^ 5 - 183283 * X ^ 6 - 114855 * X ^ 7) * Θ1
      + (8 - 224 * X + 404 * X ^ 2 + 12400 * X ^ 3 + 53970 * X ^ 4 + 125498 * X ^ 5 + 121577 * X ^ 6 + 38285 * X ^ 7) * Θ2) = 0 := by
    linear_combination (2304 * X ^ 4 - 38976 * X ^ 5 - 550848 * X ^ 6 + 9895744 * X ^ 7 + 14920608 * X ^ 8 - 220344064 * X ^ 9 - 1799934912 * X ^ 10 - 5361782720 * X ^ 11 - 5801572192 * X ^ 12 + 14132165788 * X ^ 13 + 67423544300 * X ^ 14 + 126361380808 * X ^ 15 + 136545881766 * X ^ 16 + 88053373330 * X ^ 17 + 31263818014 * X ^ 18 + 4671459130 * X ^ 19) * n_0
      + (32 * X - 1744 * X ^ 2 + 17024 * X ^ 3 + 110040 * X ^ 4 - 718680 * X ^ 5 - 6354820 * X ^ 6 - 22910304 * X ^ 7 - 32947614 * X ^ 8 + 9230878 * X ^ 9 + 130945898 * X ^ 10 + 206534111 * X ^ 11 + 128770486 * X ^ 12 + 28369185 * X ^ 13) * n_1
      + (8 - 224 * X + 404 * X ^ 2 + 12400 * X ^ 3 + 53970 * X ^ 4 + 125498 * X ^ 5 + 121577 * X ^ 6 + 38285 * X ^ 7) * n_2
  have hF : (16 - 304 * X - 384 * X ^ 2 + 11424 * X ^ 3 + 100456 * X ^ 4 + 413056 * X ^ 5 + 1061016 * X ^ 6 + 1776056 * X ^ 7 + 1885793 * X ^ 8 + 1205803 * X ^ 9 + 420147 * X ^ 10 + 61009 * X ^ 11 : ℚ⟦X⟧) ≠ 0 := by
    have hrw : (16 - 304 * X - 384 * X ^ 2 + 11424 * X ^ 3 + 100456 * X ^ 4 + 413056 * X ^ 5 + 1061016 * X ^ 6 + 1776056 * X ^ 7 + 1885793 * X ^ 8 + 1205803 * X ^ 9 + 420147 * X ^ 10 + 61009 * X ^ 11 : ℚ⟦X⟧) = C (16) + X * (-304 - 384 * X + 11424 * X ^ 2 + 100456 * X ^ 3 + 413056 * X ^ 4 + 1061016 * X ^ 5 + 1776056 * X ^ 6 + 1885793 * X ^ 7 + 1205803 * X ^ 8 + 420147 * X ^ 9 + 61009 * X ^ 10) := by
      simp only [map_ofNat, map_neg, map_one]
      ring
    rw [hrw]
    intro h
    have h0 := congrArg (coeff 0) h
    first
      | (simp only [map_add, coeff_zero_C, coeff_zero_X_mul, map_zero, add_zero] at h0; norm_num at h0)
      | (simp only [map_add, coeff_zero_C, coeff_zero_X_mul, map_zero, add_zero] at h0)
  have hD : (16 * X ^ 2 - 304 * X ^ 3 - 384 * X ^ 4 + 11424 * X ^ 5 + 100456 * X ^ 6 + 413056 * X ^ 7 + 1061016 * X ^ 8 + 1776056 * X ^ 9 + 1885793 * X ^ 10 + 1205803 * X ^ 11 + 420147 * X ^ 12 + 61009 * X ^ 13 : ℚ⟦X⟧) ≠ 0 := by
    have hrw : (16 * X ^ 2 - 304 * X ^ 3 - 384 * X ^ 4 + 11424 * X ^ 5 + 100456 * X ^ 6 + 413056 * X ^ 7 + 1061016 * X ^ 8 + 1776056 * X ^ 9 + 1885793 * X ^ 10 + 1205803 * X ^ 11 + 420147 * X ^ 12 + 61009 * X ^ 13 : ℚ⟦X⟧) = X ^ 2 * (16 - 304 * X - 384 * X ^ 2 + 11424 * X ^ 3 + 100456 * X ^ 4 + 413056 * X ^ 5 + 1061016 * X ^ 6 + 1776056 * X ^ 7 + 1885793 * X ^ 8 + 1205803 * X ^ 9 + 420147 * X ^ 10 + 61009 * X ^ 11) := by ring
    rw [hrw]
    exact mul_ne_zero (pow_ne_zero 2 X_ne_zero) hF
  have ode : -160 * X ^ 2 - 500 * X ^ 3 + 26336 * X ^ 4 + (144 * X ^ 2 + 444 * X ^ 3 - 24972 * X ^ 4 + 17428 * X ^ 5 + 61706 * X ^ 6 + 76570 * X ^ 7) * G
      - (8 - 356 * X + 1112 * X ^ 2 + 21406 * X ^ 3 + 36352 * X ^ 4 + 2750 * X ^ 5 - 183283 * X ^ 6 - 114855 * X ^ 7) * Θ1
      + (8 - 224 * X + 404 * X ^ 2 + 12400 * X ^ 3 + 53970 * X ^ 4 + 125498 * X ^ 5 + 121577 * X ^ 6 + 38285 * X ^ 7) * Θ2 = 0 :=
    (mul_eq_zero.mp keyD).resolve_left (hD)
  have key : C (144) * (X * (X * G))
      + C (444) * (X * (X * (X * G)))
      + C (-24972) * (X * (X * (X * (X * G))))
      + C (17428) * (X * (X * (X * (X * (X * G)))))
      + C (61706) * (X * (X * (X * (X * (X * (X * G))))))
      + C (76570) * (X * (X * (X * (X * (X * (X * (X * G)))))))
      + C (-8) * Θ1
      + C (356) * (X * Θ1)
      + C (-1112) * (X * (X * Θ1))
      + C (-21406) * (X * (X * (X * Θ1)))
      + C (-36352) * (X * (X * (X * (X * Θ1))))
      + C (-2750) * (X * (X * (X * (X * (X * Θ1)))))
      + C (183283) * (X * (X * (X * (X * (X * (X * Θ1))))))
      + C (114855) * (X * (X * (X * (X * (X * (X * (X * Θ1)))))))
      + C (8) * Θ2
      + C (-224) * (X * Θ2)
      + C (404) * (X * (X * Θ2))
      + C (12400) * (X * (X * (X * Θ2)))
      + C (53970) * (X * (X * (X * (X * Θ2))))
      + C (125498) * (X * (X * (X * (X * (X * Θ2)))))
      + C (121577) * (X * (X * (X * (X * (X * (X * Θ2))))))
      + C (38285) * (X * (X * (X * (X * (X * (X * (X * Θ2)))))))
      + C (-160) * (X * (X * 1))
      + C (-500) * (X * (X * (X * 1)))
      + C (26336) * (X * (X * (X * (X * 1)))) = 0 := by
    simp only [map_ofNat, map_neg, map_one]
    linear_combination ode
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have hne3 : m + 1 + 1 + 1 ≠ 0 := by omega
  have hne4 : m + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have hne5 : m + 1 + 1 + 1 + 1 + 1 ≠ 0 := by omega
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) key
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, hc2, hc1, map_zero, coeff_one, if_neg hne3, if_neg hne4, if_neg hne5] at h
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := by omega
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := by omega
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := by omega
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 := by omega
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 := by omega
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := by omega
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  push_cast at h ⊢
  linear_combination h
