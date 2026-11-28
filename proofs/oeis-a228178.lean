import OMAStatements.S_oeis_a228178
import Mathlib

/-!
Proof of Mathar's recurrence for A228178.

The coefficients of T are the Catalan numbers (coeff_T178, from T = 1 + X T^2 and the Catalan
convolution). Since X T^2 = T - 1, X^3 T^4 = X (T - 1)^2 = T - 1 - 2 X T + X, so multiplying the
equation for G by X gives X G - X^2 G = 2 T - 4 X T + X^2 T - 2 + 2 X (relG178). Comparing the
coefficients of X^(m+2): g(m+1) - g(m) = 2 C(m+2) - 4 C(m+1) + C(m) with C the Catalan numbers
(diff178). The coefficients of Mathar's recurrence sum to 0, so its left side is a combination of
the four consecutive differences, hence of C(n-3), ..., C(n+2). With (k + 2) C(k+1) = 2 (2k+1) C(k)
all of these are rational multiples of C(n-3), and the combination vanishes identically.
-/

namespace OMA.Helpers

open PowerSeries

theorem catalan_ratio178 (k : ℕ) : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  apply Nat.eq_of_mul_eq_mul_left (show 0 < k + 1 by omega)
  calc (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * ((k + 1 + 1) * catalan (k + 1)) := by
        ring_nf
    _ = (k + 1) * (k + 1).centralBinom := by rw [h1]
    _ = 2 * (2 * k + 1) * k.centralBinom := h3
    _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := by rw [h2]
    _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by ring

theorem catalan_ratioQ178 (k : ℕ) :
    (catalan (k + 1) : ℚ) = 2 * (2 * k + 1) / (k + 2) * catalan k := by
  have h := catalan_ratio178 k
  have h' : ((k : ℚ) + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by exact_mod_cast h
  have hk : (k : ℚ) + 2 ≠ 0 := by positivity
  field_simp
  linarith

theorem coeff_T178 (T : ℚ⟦X⟧) (hT : T = 1 + X * T ^ 2) : ∀ k, coeff k T = catalan k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      rw [hT]
      simp
    | succ k =>
      rw [hT, map_add, coeff_succ_X_mul, coeff_one, if_neg (by omega), zero_add, pow_two,
        coeff_mul, catalan_succ']
      push_cast
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [ih p.1 (by omega), ih p.2 (by omega)]

theorem relG178 (T G : ℚ⟦X⟧) (hT : T = 1 + X * T ^ 2)
    (hG : G * (1 - X) = X * T + 2 * X ^ 2 * T ^ 4) :
    X * G - X ^ 2 * G = C 2 * T - C 4 * (X * T) + X ^ 2 * T - C 2 + C 2 * X := by
  simp only [map_ofNat]
  linear_combination X * hG - 2 * (X * (X * T ^ 2 + T - 1) + 1) * hT

theorem diff178 (T G : ℚ⟦X⟧) (hT : T = 1 + X * T ^ 2)
    (hG : G * (1 - X) = X * T + 2 * X ^ 2 * T ^ 4) (m : ℕ) :
    coeff (m + 1) G - coeff m G =
      2 * (catalan (m + 2) : ℚ) - 4 * catalan (m + 1) + catalan m := by
  have h := congrArg (coeff (m + 2)) (relG178 T G hT hG)
  simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul', coeff_C,
    coeff_X, show m + 2 = (m + 1) + 1 by omega, coeff_T178 T hT] at h
  simp only [show 2 ≤ m + 1 + 1 by omega, if_true, show m + 1 + 1 - 2 = m by omega,
    show m + 1 + 1 ≠ 0 by omega, show m + 1 + 1 ≠ 1 by omega, if_false] at h
  linarith

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a228178.main := by
  intro T G hT hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega]
  have d5 : coeff (k + 5) G - coeff (k + 4) G =
      2 * (catalan (k + 6) : ℚ) - 4 * catalan (k + 5) + catalan (k + 4) :=
    OMA.Helpers.diff178 T G hT hG (k + 4)
  have d4 : coeff (k + 4) G - coeff (k + 3) G =
      2 * (catalan (k + 5) : ℚ) - 4 * catalan (k + 4) + catalan (k + 3) :=
    OMA.Helpers.diff178 T G hT hG (k + 3)
  have d3 : coeff (k + 3) G - coeff (k + 2) G =
      2 * (catalan (k + 4) : ℚ) - 4 * catalan (k + 3) + catalan (k + 2) :=
    OMA.Helpers.diff178 T G hT hG (k + 2)
  have d2 : coeff (k + 2) G - coeff (k + 1) G =
      2 * (catalan (k + 3) : ℚ) - 4 * catalan (k + 2) + catalan (k + 1) :=
    OMA.Helpers.diff178 T G hT hG (k + 1)
  have r2 : (catalan (k + 2) : ℚ) =
      2 * (2 * ((k + 1 : ℕ) : ℚ) + 1) / (((k + 1 : ℕ) : ℚ) + 2) * catalan (k + 1) :=
    OMA.Helpers.catalan_ratioQ178 (k + 1)
  have r3 : (catalan (k + 3) : ℚ) =
      2 * (2 * ((k + 2 : ℕ) : ℚ) + 1) / (((k + 2 : ℕ) : ℚ) + 2) * catalan (k + 2) :=
    OMA.Helpers.catalan_ratioQ178 (k + 2)
  have r4 : (catalan (k + 4) : ℚ) =
      2 * (2 * ((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) + 2) * catalan (k + 3) :=
    OMA.Helpers.catalan_ratioQ178 (k + 3)
  have r5 : (catalan (k + 5) : ℚ) =
      2 * (2 * ((k + 4 : ℕ) : ℚ) + 1) / (((k + 4 : ℕ) : ℚ) + 2) * catalan (k + 4) :=
    OMA.Helpers.catalan_ratioQ178 (k + 4)
  have r6 : (catalan (k + 6) : ℚ) =
      2 * (2 * ((k + 5 : ℕ) : ℚ) + 1) / (((k + 5 : ℕ) : ℚ) + 2) * catalan (k + 5) :=
    OMA.Helpers.catalan_ratioQ178 (k + 5)
  have key : 2 * (((k + 4 : ℕ) : ℚ) + 3) * coeff (k + 4 + 1) G +
      2 * (-7 * ((k + 4 : ℕ) : ℚ) - 11) * coeff (k + 4) G +
      (29 * ((k + 4 : ℕ) : ℚ) + 7) * coeff (k + 3) G +
      (-21 * ((k + 4 : ℕ) : ℚ) + 19) * coeff (k + 2) G +
      2 * (2 * ((k + 4 : ℕ) : ℚ) - 5) * coeff (k + 1) G =
      (2 * (k + 4) + 6) * (coeff (k + 5) G - coeff (k + 4) G) -
        (12 * (k + 4) + 16) * (coeff (k + 4) G - coeff (k + 3) G) +
        (17 * (k + 4) - 9) * (coeff (k + 3) G - coeff (k + 2) G) -
        (4 * (k + 4) - 10) * (coeff (k + 2) G - coeff (k + 1) G) := by
    rw [show k + 4 + 1 = k + 5 by omega]
    push_cast
    ring
  rw [key, d5, d4, d3, d2, r6, r5, r4, r3, r2]
  have h1 : (k : ℚ) + 1 + 2 ≠ 0 := by positivity
  have h2 : ((k + 2 : ℕ) : ℚ) + 2 ≠ 0 := by positivity
  have h3 : ((k + 3 : ℕ) : ℚ) + 2 ≠ 0 := by positivity
  have h4 : ((k + 4 : ℕ) : ℚ) + 2 ≠ 0 := by positivity
  have h5 : ((k + 5 : ℕ) : ℚ) + 2 ≠ 0 := by positivity
  push_cast at h1 h2 h3 h4 h5 ⊢
  field_simp
  ring
