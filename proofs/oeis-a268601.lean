import OMAStatements.S_oeis_a268601

/-!
# Proof of the recurrence for OEIS A268601

The hypotheses make `T`, `W` algebraic over `ℚ(X)`: `T ^ 2 = 1 - 4 * X`, `W ^ 2 = 1 + 4 * X`; and `G` is given by `G * (2 * T * (4 - 2 * W)) = (4 - 2 * W) - 2 * T`.
The hypotheses on constant terms are not needed: the argument holds for every solution of these equations.

Write `θ = X d/dX`, so that the coefficient of `X ^ k` in `θ f` is `k` times that of `f`. The recurrence says that
the coefficient of `X ^ n` in `L G` vanishes for `n ≥ 4`, where `L = Σ_i X ^ i c_i(θ + i)` and `c_i(n)` is the
coefficient of `a(n - i)`. The proof shows that `L G` is a polynomial of degree less than 4:

* differentiating the equation of each algebraic series and multiplying by the inverse of the separant
  expresses its derivative in the basis of monomials in `T`, `W`, with a denominator in `ℚ[X]` (`n1_*`);
* `G` is put in that normal form (`n_0`), then `θ G`, `θ ^ 2 G` by differentiating the previous
  normal form and eliminating the derivatives of the algebraic series (`n_1`, ...);
* a combination of these normal forms gives `D * (L G - p) = 0` for a nonzero polynomial `D` in `X`
  and an explicit polynomial `p`, hence `L G = p`; the coefficient of `X ^ n` is the recurrence.

Here `p = 12 * X ^ 2 + 48 * X ^ 3` and `D = 432 - 3456 * X - 4608 * X ^ 2 + 100352 * X ^ 3 - 180224 * X ^ 4 - 557056 * X ^ 5 + 2228224 * X ^ 6 - 2621440 * X ^ 7 + 1048576 * X ^ 8`.

Every step is an explicit polynomial identity checked by `linear_combination`.
-/

namespace OMA.S_oeis_a268601

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

end OMA.S_oeis_a268601

set_option maxHeartbeats 3200000 in
open PowerSeries OMA.S_oeis_a268601 in
theorem OMA.solution : type_of% @OMA.S_oeis_a268601.main := by
  intro T W G h1 _ h2 _ h3
  -- a hypothesis on the constant term of `G` may or may not precede `n`; it is not needed
  first
    | intro _ n hn
    | intro n hn
  have hd1 : 2 * T * d⁄dX ℚ T =
      -4 := by
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
    have e2 : d⁄dX ℚ (1 - 4 * X : ℚ⟦X⟧) =
        -4 := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) h1).trans e2)
  have n1_1 : -(2 - 8 * X) * d⁄dX ℚ T =
      4 * T := by
    linear_combination -T * hd1 + (2 * d⁄dX ℚ T) * h1
  have hd2 : 2 * W * d⁄dX ℚ W =
      4 := by
    have e1 : d⁄dX ℚ (W ^ 2 : ℚ⟦X⟧) =
        2 * W * d⁄dX ℚ W := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ (1 + 4 * X : ℚ⟦X⟧) =
        4 := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) h2).trans e2)
  have n1_2 : (2 + 8 * X) * d⁄dX ℚ W =
      4 * W := by
    linear_combination W * hd2 - (2 * d⁄dX ℚ W) * h2
  have n_0 : (12 - 64 * X + 64 * X ^ 2) * G =
      -4 + 16 * X + (6 - 8 * X) * T - (2 - 8 * X) * W := by
    linear_combination (2 * T + T * W) * h3 + (-4 - 2 * W - (12 - 16 * X) * G) * h1 + (-2 * T + 4 * T ^ 2 * G) * h2
  obtain ⟨Θ1, hΘ1, hc1⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ G ∧ ∀ k, coeff k Θ = k * coeff k G :=
    ⟨_, rfl, coeff_theta G⟩
  have hdn_0 : -(64 - 128 * X) * G + (12 - 64 * X + 64 * X ^ 2) * d⁄dX ℚ G =
      16 - 8 * T + 8 * W + (6 - 8 * X) * d⁄dX ℚ T - (2 - 8 * X) * d⁄dX ℚ W := by
    have e1 : d⁄dX ℚ ((12 - 64 * X + 64 * X ^ 2) * G : ℚ⟦X⟧) =
        -(64 - 128 * X) * G + (12 - 64 * X + 64 * X ^ 2) * d⁄dX ℚ G := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ (-4 + 16 * X + (6 - 8 * X) * T - (2 - 8 * X) * W : ℚ⟦X⟧) =
        16 - 8 * T + 8 * W + (6 - 8 * X) * d⁄dX ℚ T - (2 - 8 * X) * d⁄dX ℚ W := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) n_0).trans e2)
  have n_1 : (72 - 480 * X - 256 * X ^ 2 + 7168 * X ^ 3 - 14336 * X ^ 4 + 8192 * X ^ 5) * Θ1 =
      -32 * X + 128 * X ^ 2 + 512 * X ^ 3 - 2048 * X ^ 4 + (72 * X + 96 * X ^ 2 - 640 * X ^ 3 + 512 * X ^ 4) * T
      - (40 * X - 288 * X ^ 2 + 384 * X ^ 3 + 512 * X ^ 4) * W := by
    rw [hΘ1]
    linear_combination (6 * X - 8 * X ^ 2 - 96 * X ^ 3 + 128 * X ^ 4) * hdn_0 + (-18 * X - 24 * X ^ 2 + 160 * X ^ 3 - 128 * X ^ 4) * n1_1
      + (-6 * X + 56 * X ^ 2 - 160 * X ^ 3 + 128 * X ^ 4) * n1_2 + (32 * X + 64 * X ^ 2 - 256 * X ^ 3) * n_0
  obtain ⟨Θ2, hΘ2, hc2⟩ : ∃ Θ : ℚ⟦X⟧, Θ = X * d⁄dX ℚ Θ1 ∧ ∀ k, coeff k Θ = k * coeff k Θ1 :=
    ⟨_, rfl, coeff_theta Θ1⟩
  have hdn_1 : -(480 + 512 * X - 21504 * X ^ 2 + 57344 * X ^ 3 - 40960 * X ^ 4) * Θ1
      + (72 - 480 * X - 256 * X ^ 2 + 7168 * X ^ 3 - 14336 * X ^ 4 + 8192 * X ^ 5) * d⁄dX ℚ Θ1 =
      -32 + 256 * X + 1536 * X ^ 2 - 8192 * X ^ 3 + (72 + 192 * X - 1920 * X ^ 2 + 2048 * X ^ 3) * T
      - (40 - 576 * X + 1152 * X ^ 2 + 2048 * X ^ 3) * W + (72 * X + 96 * X ^ 2 - 640 * X ^ 3 + 512 * X ^ 4) * d⁄dX ℚ T
      - (40 * X - 288 * X ^ 2 + 384 * X ^ 3 + 512 * X ^ 4) * d⁄dX ℚ W := by
    have e1 : d⁄dX ℚ ((72 - 480 * X - 256 * X ^ 2 + 7168 * X ^ 3 - 14336 * X ^ 4 + 8192 * X ^ 5) * Θ1 : ℚ⟦X⟧) =
        -(480 + 512 * X - 21504 * X ^ 2 + 57344 * X ^ 3 - 40960 * X ^ 4) * Θ1
        + (72 - 480 * X - 256 * X ^ 2 + 7168 * X ^ 3 - 14336 * X ^ 4 + 8192 * X ^ 5) * d⁄dX ℚ Θ1 := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    have e2 : d⁄dX ℚ (-32 * X + 128 * X ^ 2 + 512 * X ^ 3 - 2048 * X ^ 4 + (72 * X + 96 * X ^ 2 - 640 * X ^ 3 + 512 * X ^ 4) * T
        - (40 * X - 288 * X ^ 2 + 384 * X ^ 3 + 512 * X ^ 4) * W : ℚ⟦X⟧) =
        -32 + 256 * X + 1536 * X ^ 2 - 8192 * X ^ 3 + (72 + 192 * X - 1920 * X ^ 2 + 2048 * X ^ 3) * T
        - (40 - 576 * X + 1152 * X ^ 2 + 2048 * X ^ 3) * W + (72 * X + 96 * X ^ 2 - 640 * X ^ 3 + 512 * X ^ 4) * d⁄dX ℚ T
        - (40 * X - 288 * X ^ 2 + 384 * X ^ 3 + 512 * X ^ 4) * d⁄dX ℚ W := by
      first
        | (simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]; ring)
        | simp only [map_sub, map_add, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
            Derivation.map_one_eq_zero, derivative_X, d_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
            Nat.reduceSub, pow_one]
        | rfl
    exact e1.symm.trans ((congrArg (d⁄dX ℚ) n_1).trans e2)
  have n_2 : (432 - 3456 * X - 4608 * X ^ 2 + 100352 * X ^ 3 - 180224 * X ^ 4 - 557056 * X ^ 5 + 2228224 * X ^ 6 - 2621440 * X ^ 7 + 1048576 * X ^ 8) * Θ2 =
      -192 * X + 512 * X ^ 2 + 7168 * X ^ 3 - 16384 * X ^ 4 - 81920 * X ^ 5
      + 131072 * X ^ 6 + 262144 * X ^ 7 + (432 * X + 2592 * X ^ 2 - 1152 * X ^ 3 - 19456 * X ^ 4 + 8192 * X ^ 5 + 40960 * X ^ 6 - 32768 * X ^ 7) * T
      - (240 * X - 1696 * X ^ 2 + 384 * X ^ 3 + 5120 * X ^ 4 + 65536 * X ^ 5 - 172032 * X ^ 6 - 32768 * X ^ 7) * W := by
    rw [hΘ2]
    linear_combination (6 * X - 8 * X ^ 2 - 96 * X ^ 3 + 128 * X ^ 4) * hdn_1 + (-216 * X ^ 2 - 864 * X ^ 3 + 2304 * X ^ 4 + 5120 * X ^ 5 - 14336 * X ^ 6 + 8192 * X ^ 7) * n1_1
      + (-120 * X ^ 2 + 1504 * X ^ 3 - 6400 * X ^ 4 + 9216 * X ^ 5 + 2048 * X ^ 6 - 8192 * X ^ 7) * n1_2
      + (40 * X + 256 * X ^ 2 - 640 * X ^ 3) * n_1
  have keyD : (432 - 3456 * X - 4608 * X ^ 2 + 100352 * X ^ 3 - 180224 * X ^ 4 - 557056 * X ^ 5 + 2228224 * X ^ 6 - 2621440 * X ^ 7 + 1048576 * X ^ 8) * (-12 * X ^ 2 - 48 * X ^ 3 - (68 * X ^ 2 + 160 * X ^ 3 + 576 * X ^ 4) * G
      - (3 - 56 * X - 112 * X ^ 2 + 1536 * X ^ 4) * Θ1 + (3 - 40 * X + 640 * X ^ 3 - 768 * X ^ 4) * Θ2) = 0 := by
    linear_combination (-2448 * X ^ 2 + 768 * X ^ 3 + 68608 * X ^ 4 + 20480 * X ^ 5 - 352256 * X ^ 6 - 1245184 * X ^ 7 - 1310720 * X ^ 8 + 11534336 * X ^ 9 - 9437184 * X ^ 10) * n_0
      + (-18 + 360 * X + 512 * X ^ 2 - 6656 * X ^ 3 - 12800 * X ^ 4 + 26624 * X ^ 5 + 147456 * X ^ 6 - 196608 * X ^ 7) * n_1
      + (3 - 40 * X + 640 * X ^ 3 - 768 * X ^ 4) * n_2
  have hF : (432 - 3456 * X - 4608 * X ^ 2 + 100352 * X ^ 3 - 180224 * X ^ 4 - 557056 * X ^ 5 + 2228224 * X ^ 6 - 2621440 * X ^ 7 + 1048576 * X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    have hrw : (432 - 3456 * X - 4608 * X ^ 2 + 100352 * X ^ 3 - 180224 * X ^ 4 - 557056 * X ^ 5 + 2228224 * X ^ 6 - 2621440 * X ^ 7 + 1048576 * X ^ 8 : ℚ⟦X⟧) = C (432) + X * (-3456 - 4608 * X + 100352 * X ^ 2 - 180224 * X ^ 3 - 557056 * X ^ 4 + 2228224 * X ^ 5 - 2621440 * X ^ 6 + 1048576 * X ^ 7) := by
      simp only [map_ofNat, map_neg, map_one]
      ring
    rw [hrw]
    intro h
    have h0 := congrArg (coeff 0) h
    first
      | (simp only [map_add, coeff_zero_C, coeff_zero_X_mul, map_zero, add_zero] at h0; norm_num at h0)
      | (simp only [map_add, coeff_zero_C, coeff_zero_X_mul, map_zero, add_zero] at h0)
  have ode : -12 * X ^ 2 - 48 * X ^ 3 - (68 * X ^ 2 + 160 * X ^ 3 + 576 * X ^ 4) * G
      - (3 - 56 * X - 112 * X ^ 2 + 1536 * X ^ 4) * Θ1 + (3 - 40 * X + 640 * X ^ 3 - 768 * X ^ 4) * Θ2 = 0 :=
    (mul_eq_zero.mp keyD).resolve_left (hF)
  have key : C (-68) * (X * (X * G))
      + C (-160) * (X * (X * (X * G)))
      + C (-576) * (X * (X * (X * (X * G))))
      + C (-3) * Θ1
      + C (56) * (X * Θ1)
      + C (112) * (X * (X * Θ1))
      + C (-1536) * (X * (X * (X * (X * Θ1))))
      + C (3) * Θ2
      + C (-40) * (X * Θ2)
      + C (640) * (X * (X * (X * Θ2)))
      + C (-768) * (X * (X * (X * (X * Θ2))))
      + C (-12) * (X * (X * 1))
      + C (-48) * (X * (X * (X * 1))) = 0 := by
    simp only [map_ofNat, map_neg, map_one]
    linear_combination ode
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have hne1 : m + 1 ≠ 0 := by omega
  have hne2 : m + 1 + 1 ≠ 0 := by omega
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) key
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, hc2, hc1, map_zero, coeff_one, if_neg hne1, if_neg hne2] at h
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := by omega
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := by omega
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := by omega
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := by omega
  rw [e1, e2, e3, e4]
  push_cast at h ⊢
  linear_combination h
