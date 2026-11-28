import OMAStatements.S_oeis_a157002
import Mathlib

/-!
Proof of Mathar's recurrence for A257388.

The defining recursion says the generating function satisfies A = T + X^2 A^2 with (1 - 4X) T = 1, so
H = X^2 (1 - 4X) A satisfies H^2 = (1 - 4X) H - X^2 (1 - 4X). The recurrence obtained for H is the
stated recurrence at n minus 4 times the stated recurrence at n - 1, so the statement follows by induction.
For a power series with such a quadratic equation, differentiating and eliminating H^2 gives a
first-order linear differential equation, hence a linear recurrence for the coefficients of H
(theorem rec_of_quadratic); the finitely many small cases are checked directly.
-/

namespace OMA.QC


open PowerSeries Finset

/-- Coefficients of the square of a power series without constant term. -/
lemma coeff_sq (a : ℕ → ℤ) (h0 : a 0 = 0) (n : ℕ) :
    coeff (n + 2) ((PowerSeries.mk a) ^ 2) = ∑ k ∈ range (n + 1), a (k + 1) * a (n + 1 - k) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [coeff_mk, h0, zero_mul, add_zero]
  rw [show n + 2 - (n + 1 + 1) = 0 by omega, h0, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n + 1 := Finset.mem_range.mp hk
  have e : n + 2 - (k + 1) = n + 1 - k := by omega
  rw [e]

lemma coeff_sq_zero (a : ℕ → ℤ) (h0 : a 0 = 0) : coeff 0 ((PowerSeries.mk a) ^ 2) = 0 := by
  rw [pow_two, coeff_mul]
  simp [h0]

lemma coeff_sq_one (a : ℕ → ℤ) (h0 : a 0 = 0) : coeff 1 ((PowerSeries.mk a) ^ 2) = 0 := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, h0]

/-- If the generating function G of `a` satisfies G^2 = L G - R with L = 1 + l1 X + l2 X^2 and
R = r1 X + r2 X^2 + r3 X^3 + r4 X^4, then `a` satisfies a linear recurrence of order four with
linear coefficients. -/
theorem rec_of_quadratic (a : ℕ → ℤ) (l1 l2 r1 r2 r3 r4 : ℤ)
    (hE : (PowerSeries.mk a) ^ 2 = (1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
      - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) (N : ℕ) :
    ((N : ℤ) + 6) * a (N + 6) + (l1 - 2 * r1) * (2 * (N : ℤ) + 9) * a (N + 5)
      + (l1 ^ 2 + 2 * l2 - 4 * r2) * ((N : ℤ) + 3) * a (N + 4)
      + (l1 * l2 - 2 * r3) * (2 * (N : ℤ) + 3) * a (N + 3)
      + (l2 ^ 2 - 4 * r4) * (N : ℤ) * a (N + 2) = 0 := by
  set G : PowerSeries ℤ := PowerSeries.mk a with hG
  set G' : PowerSeries ℤ := derivative ℤ G with hG'
  have hD : 2 * G * G' = (C l1 + 2 * C l2 * X) * G + (1 + C l1 * X + C l2 * X ^ 2) * G'
      - (C r1 + 2 * C r2 * X + 3 * C r3 * X ^ 2 + 4 * C r4 * X ^ 3) := by
    have h := congrArg (derivative ℤ) hE
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, derivative_C,
      derivative_X, smul_eq_mul, nsmul_eq_mul, Derivation.map_one_eq_zero] at h
    simp only [← hG'] at h
    push_cast at h
    linear_combination h
  have hODE : G' + C (2 * l1 - 4 * r1) * (X * G') + C (l1 ^ 2 + 2 * l2 - 4 * r2) * (X ^ 2 * G')
      + C (2 * l1 * l2 - 4 * r3) * (X ^ 3 * G') + C (l2 ^ 2 - 4 * r4) * (X ^ 4 * G')
      - (C (l1 - 2 * r1) * G + C (l1 ^ 2 + 2 * l2 - 4 * r2) * (X * G)
        + C (3 * l1 * l2 - 6 * r3) * (X ^ 2 * G) + C (2 * l2 ^ 2 - 8 * r4) * (X ^ 3 * G))
      - (C r1 + C (2 * r2 - l1 * r1) * X + C (3 * r3 - 3 * l2 * r1) * X ^ 2
        + C (l1 * r3 - 2 * l2 * r2 + 4 * r4) * X ^ 3 + C (2 * l1 * r4 - l2 * r3) * X ^ 4) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination (2 * (C l1 + 2 * C l2 * X) - 4 * G') * hE
      - ((1 + C l1 * X + C l2 * X ^ 2) - 2 * G) * hD
  have h := congrArg (coeff (N + 5)) hODE
  have d0 : coeff (N + 5) G' = a (N + 6) * ((N : ℤ) + 6) := by
    rw [hG', coeff_derivative, hG, coeff_mk]; push_cast; ring
  have d1 : coeff (N + 5) (X * G') = a (N + 5) * ((N : ℤ) + 5) := by
    rw [coeff_succ_X_mul, hG', coeff_derivative, hG, coeff_mk]; push_cast; ring
  have d2 : coeff (N + 5) (X ^ 2 * G') = a (N + 4) * ((N : ℤ) + 4) := by
    rw [show N + 5 = N + 3 + 2 from rfl, coeff_X_pow_mul, hG', coeff_derivative, hG, coeff_mk]
    push_cast; ring
  have d3 : coeff (N + 5) (X ^ 3 * G') = a (N + 3) * ((N : ℤ) + 3) := by
    rw [show N + 5 = N + 2 + 3 from rfl, coeff_X_pow_mul, hG', coeff_derivative, hG, coeff_mk]
    push_cast; ring
  have d4 : coeff (N + 5) (X ^ 4 * G') = a (N + 2) * ((N : ℤ) + 2) := by
    rw [show N + 5 = N + 1 + 4 from rfl, coeff_X_pow_mul, hG', coeff_derivative, hG, coeff_mk]
    push_cast; ring
  have g0 : coeff (N + 5) G = a (N + 5) := by rw [hG, coeff_mk]
  have g1 : coeff (N + 5) (X * G) = a (N + 4) := by rw [coeff_succ_X_mul, hG, coeff_mk]
  have g2 : coeff (N + 5) (X ^ 2 * G) = a (N + 3) := by
    rw [show N + 5 = N + 3 + 2 from rfl, coeff_X_pow_mul, hG, coeff_mk]
  have g3 : coeff (N + 5) (X ^ 3 * G) = a (N + 2) := by
    rw [show N + 5 = N + 2 + 3 from rfl, coeff_X_pow_mul, hG, coeff_mk]
  have s0 : coeff (N + 5) (C r1 : PowerSeries ℤ) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have s1 : coeff (N + 5) (C (2 * r2 - l1 * r1) * X : PowerSeries ℤ) = 0 := by
    rw [coeff_C_mul, coeff_X, if_neg (by omega), mul_zero]
  have s2 : coeff (N + 5) (C (3 * r3 - 3 * l2 * r1) * X ^ 2 : PowerSeries ℤ) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have s3 : coeff (N + 5) (C (l1 * r3 - 2 * l2 * r2 + 4 * r4) * X ^ 3 : PowerSeries ℤ) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have s4 : coeff (N + 5) (C (2 * l1 * r4 - l2 * r3) * X ^ 4 : PowerSeries ℤ) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, d0, d1, d2, d3, d4, g0, g1, g2, g3,
    s0, s1, s2, s3, s4, LinearMap.map_zero] at h
  linear_combination h


/-- The right-hand side L G - R, expanded into monomial multiples of G. -/
lemma rhs_expand (a : ℕ → ℤ) (l1 l2 r1 r2 r3 r4 : ℤ) :
    (1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
      - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)
    = PowerSeries.mk a + C l1 * (X * PowerSeries.mk a) + C l2 * (X ^ 2 * PowerSeries.mk a)
      - C r1 * X - C r2 * X ^ 2 - C r3 * X ^ 3 - C r4 * X ^ 4 := by
  ring

lemma coeff_rhs_big (a : ℕ → ℤ) (l1 l2 r1 r2 r3 r4 : ℤ) (n : ℕ) :
    coeff (n + 5) ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
      - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4))
    = a (n + 5) + l1 * a (n + 4) + l2 * a (n + 3) := by
  rw [rhs_expand]
  have e2 : coeff (n + 5) (X ^ 2 * PowerSeries.mk a) = a (n + 3) := by
    rw [show n + 5 = n + 3 + 2 from rfl, coeff_X_pow_mul, coeff_mk]
  simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_mk, e2,
    coeff_X, coeff_X_pow]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  ring

lemma coeff_rhs_small (a : ℕ → ℤ) (l1 l2 r1 r2 r3 r4 : ℤ) (h0 : a 0 = 0) :
    coeff 0 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) = 0
    ∧ coeff 1 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) = a 1 - r1
    ∧ coeff 2 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) = a 2 + l1 * a 1 - r2
    ∧ coeff 3 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) = a 3 + l1 * a 2 + l2 * a 1 - r3
    ∧ coeff 4 ((1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
        - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4))
        = a 4 + l1 * a 3 + l2 * a 2 - r4 := by
  rw [rhs_expand]
  have x0 : coeff 0 (X * PowerSeries.mk a) = 0 := coeff_zero_X_mul _
  have x1 : coeff 1 (X * PowerSeries.mk a) = a 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
  have x2 : coeff 2 (X * PowerSeries.mk a) = a 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
  have x3 : coeff 3 (X * PowerSeries.mk a) = a 2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
  have x4 : coeff 4 (X * PowerSeries.mk a) = a 3 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
  have y0 : coeff 0 (X ^ 2 * PowerSeries.mk a) = 0 := by
    rw [coeff_X_pow_mul']; simp
  have y1 : coeff 1 (X ^ 2 * PowerSeries.mk a) = 0 := by
    rw [coeff_X_pow_mul']; simp
  have y2 : coeff 2 (X ^ 2 * PowerSeries.mk a) = a 0 := by
    rw [show (2 : ℕ) = 0 + 2 from rfl, coeff_X_pow_mul, coeff_mk]
  have y3 : coeff 3 (X ^ 2 * PowerSeries.mk a) = a 1 := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, coeff_X_pow_mul, coeff_mk]
  have y4 : coeff 4 (X ^ 2 * PowerSeries.mk a) = a 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, coeff_X_pow_mul, coeff_mk]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, coeff_mk, x0, x1, x2, x3, x4,
      y0, y1, y2, y3, y4, coeff_X, coeff_X_pow, h0]
     norm_num)


/-- Coefficients of the square of a power series, as a convolution over `Fin`. -/
lemma coeff_sq_fin (a : ℕ → ℤ) (n : ℕ) :
    coeff n ((PowerSeries.mk a) ^ 2) = ∑ k : Fin (n + 1), a k * a (n - k) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk]
  exact (Fin.sum_univ_eq_sum_range (fun k => a k * a (n - k)) (n + 1)).symm

end OMA.QC

namespace OMA.P157002

open PowerSeries

noncomputable def G : PowerSeries ℤ := PowerSeries.mk OMA.S_oeis_a157002.a

lemma hG : G = 1 - X + X * G ^ 2 + X * (X * G ^ 2) := by
  ext n
  rcases n with _ | _ | n
  · simp [G, OMA.S_oeis_a157002.a]
  · rw [show (1 : ℕ) = 0 + 1 from rfl]
    simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, coeff_succ_X_mul,
      coeff_zero_X_mul, G, coeff_mk, OMA.QC.coeff_sq_fin, coeff_one, coeff_X]
    simp [OMA.S_oeis_a157002.a]
  · simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, coeff_succ_X_mul, G, coeff_mk,
      OMA.QC.coeff_sq_fin, coeff_one, coeff_X]
    rw [OMA.S_oeis_a157002.a.eq_3]
    simp

noncomputable def H : PowerSeries ℤ := X * (1 + X) * G

lemma hH : (PowerSeries.mk fun n => coeff n H) ^ 2
    = (1 + C 0 * X + C 0 * X ^ 2) * (PowerSeries.mk fun n => coeff n H)
      - (C 1 * X + C 0 * X ^ 2 + C (-1) * X ^ 3 + C 0 * X ^ 4) := by
  have hmk : (PowerSeries.mk fun n => coeff n H) = H := by
    ext n
    simp
  rw [hmk]
  have h1 := hG
  unfold H
  simp only [map_neg, map_one, map_zero] at *
  linear_combination (-(X * (1 + X))) * h1

lemma coeff_H (j : ℕ) : coeff (j + 2) H = OMA.S_oeis_a157002.a (j + 1) + OMA.S_oeis_a157002.a j := by
  have e : H = X * G + X ^ 2 * G := by
    unfold H
    ring
  rw [e, LinearMap.map_add, coeff_X_pow_mul, show j + 2 = j + 1 + 1 from rfl, coeff_succ_X_mul]
  simp only [G, coeff_mk]


lemma v0 : OMA.S_oeis_a157002.a 0 = 1 := OMA.S_oeis_a157002.a.eq_1
lemma v1 : OMA.S_oeis_a157002.a 1 = 0 := OMA.S_oeis_a157002.a.eq_2
lemma v2 : OMA.S_oeis_a157002.a 2 = 1 := by
  have h := OMA.S_oeis_a157002.a.eq_3 0
  simpa [Fin.sum_univ_succ, v0, v1] using h
lemma v3 : OMA.S_oeis_a157002.a 3 = 2 := by
  have h := OMA.S_oeis_a157002.a.eq_3 1
  simpa [Fin.sum_univ_succ, v0, v1, v2] using h
lemma v4 : OMA.S_oeis_a157002.a 4 = 6 := by
  have h := OMA.S_oeis_a157002.a.eq_3 2
  simpa [Fin.sum_univ_succ, v0, v1, v2, v3] using h

end OMA.P157002

theorem OMA.solution : type_of% @OMA.S_oeis_a157002.main := by
  intro n hn
  rcases Nat.lt_or_ge n 5 with hlt | hge
  · interval_cases n <;> norm_num [OMA.P157002.v0, OMA.P157002.v1, OMA.P157002.v2, OMA.P157002.v3, OMA.P157002.v4]
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 5 := ⟨n - 5, by omega⟩
    have h := OMA.QC.rec_of_quadratic (fun n => PowerSeries.coeff n OMA.P157002.H) 0 0 1 0 (-1) 0 OMA.P157002.hH N
    have c6 := OMA.P157002.coeff_H (N + 4)
    have c5 := OMA.P157002.coeff_H (N + 3)
    have c4 := OMA.P157002.coeff_H (N + 2)
    have c3 := OMA.P157002.coeff_H (N + 1)
    have c2 := OMA.P157002.coeff_H N
    simp only [show N + 4 + 2 = N + 6 from rfl, show N + 3 + 2 = N + 5 from rfl,
      show N + 2 + 2 = N + 4 from rfl, show N + 1 + 2 = N + 3 from rfl,
      show N + 4 + 1 = N + 5 from rfl,
      show N + 3 + 1 = N + 4 from rfl, show N + 2 + 1 = N + 3 from rfl,
      show N + 1 + 1 = N + 2 from rfl] at c6 c5 c4 c3 c2
    simp only [c6, c5, c4, c3, c2] at h
    have e1 : N + 5 - 1 = N + 4 := by omega
    have e2 : N + 5 - 2 = N + 3 := by omega
    have e3 : N + 5 - 3 = N + 2 := by omega
    have e4 : N + 5 - 4 = N + 1 := by omega
    simp only [e1, e2, e3, e4]
    push_cast
    linear_combination h
