import OMAStatements.S_oeis_a025275
import Mathlib

namespace OMA.QC025275


open PowerSeries Finset

/-- Coefficients of the square of a power series without constant term. -/
lemma coeff_sq (a : ℕ → ℚ) (h0 : a 0 = 0) (n : ℕ) :
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

lemma coeff_sq_zero (a : ℕ → ℚ) (h0 : a 0 = 0) : coeff 0 ((PowerSeries.mk a) ^ 2) = 0 := by
  rw [pow_two, coeff_mul]
  simp [h0]

lemma coeff_sq_one (a : ℕ → ℚ) (h0 : a 0 = 0) : coeff 1 ((PowerSeries.mk a) ^ 2) = 0 := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, h0]

/-- If the generating function G of `a` satisfies G^2 = L G - R with L = 1 + l1 X + l2 X^2 and
R = r1 X + r2 X^2 + r3 X^3 + r4 X^4, then `a` satisfies a linear recurrence of order four with
linear coefficients. -/
theorem rec_of_quadratic (a : ℕ → ℚ) (l1 l2 r1 r2 r3 r4 : ℚ)
    (hE : (PowerSeries.mk a) ^ 2 = (1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
      - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)) (N : ℕ) :
    ((N : ℚ) + 6) * a (N + 6) + (l1 - 2 * r1) * (2 * (N : ℚ) + 9) * a (N + 5)
      + (l1 ^ 2 + 2 * l2 - 4 * r2) * ((N : ℚ) + 3) * a (N + 4)
      + (l1 * l2 - 2 * r3) * (2 * (N : ℚ) + 3) * a (N + 3)
      + (l2 ^ 2 - 4 * r4) * (N : ℚ) * a (N + 2) = 0 := by
  set G : PowerSeries ℚ := PowerSeries.mk a with hG
  set G' : PowerSeries ℚ := derivative ℚ G with hG'
  have hD : 2 * G * G' = (C l1 + 2 * C l2 * X) * G + (1 + C l1 * X + C l2 * X ^ 2) * G'
      - (C r1 + 2 * C r2 * X + 3 * C r3 * X ^ 2 + 4 * C r4 * X ^ 3) := by
    have h := congrArg (derivative ℚ) hE
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
  have d0 : coeff (N + 5) G' = a (N + 6) * ((N : ℚ) + 6) := by
    rw [hG', coeff_derivative, hG, coeff_mk]; push_cast; ring
  have d1 : coeff (N + 5) (X * G') = a (N + 5) * ((N : ℚ) + 5) := by
    rw [coeff_succ_X_mul, hG', coeff_derivative, hG, coeff_mk]; push_cast; ring
  have d2 : coeff (N + 5) (X ^ 2 * G') = a (N + 4) * ((N : ℚ) + 4) := by
    rw [show N + 5 = N + 3 + 2 from rfl, coeff_X_pow_mul, hG', coeff_derivative, hG, coeff_mk]
    push_cast; ring
  have d3 : coeff (N + 5) (X ^ 3 * G') = a (N + 3) * ((N : ℚ) + 3) := by
    rw [show N + 5 = N + 2 + 3 from rfl, coeff_X_pow_mul, hG', coeff_derivative, hG, coeff_mk]
    push_cast; ring
  have d4 : coeff (N + 5) (X ^ 4 * G') = a (N + 2) * ((N : ℚ) + 2) := by
    rw [show N + 5 = N + 1 + 4 from rfl, coeff_X_pow_mul, hG', coeff_derivative, hG, coeff_mk]
    push_cast; ring
  have g0 : coeff (N + 5) G = a (N + 5) := by rw [hG, coeff_mk]
  have g1 : coeff (N + 5) (X * G) = a (N + 4) := by rw [coeff_succ_X_mul, hG, coeff_mk]
  have g2 : coeff (N + 5) (X ^ 2 * G) = a (N + 3) := by
    rw [show N + 5 = N + 3 + 2 from rfl, coeff_X_pow_mul, hG, coeff_mk]
  have g3 : coeff (N + 5) (X ^ 3 * G) = a (N + 2) := by
    rw [show N + 5 = N + 2 + 3 from rfl, coeff_X_pow_mul, hG, coeff_mk]
  have s0 : coeff (N + 5) (C r1 : PowerSeries ℚ) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have s1 : coeff (N + 5) (C (2 * r2 - l1 * r1) * X : PowerSeries ℚ) = 0 := by
    rw [coeff_C_mul, coeff_X, if_neg (by omega), mul_zero]
  have s2 : coeff (N + 5) (C (3 * r3 - 3 * l2 * r1) * X ^ 2 : PowerSeries ℚ) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have s3 : coeff (N + 5) (C (l1 * r3 - 2 * l2 * r2 + 4 * r4) * X ^ 3 : PowerSeries ℚ) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have s4 : coeff (N + 5) (C (2 * l1 * r4 - l2 * r3) * X ^ 4 : PowerSeries ℚ) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, d0, d1, d2, d3, d4, g0, g1, g2, g3,
    s0, s1, s2, s3, s4, LinearMap.map_zero] at h
  linear_combination h


/-- The right-hand side L G - R, expanded into monomial multiples of G. -/
lemma rhs_expand (a : ℕ → ℚ) (l1 l2 r1 r2 r3 r4 : ℚ) :
    (1 + C l1 * X + C l2 * X ^ 2) * PowerSeries.mk a
      - (C r1 * X + C r2 * X ^ 2 + C r3 * X ^ 3 + C r4 * X ^ 4)
    = PowerSeries.mk a + C l1 * (X * PowerSeries.mk a) + C l2 * (X ^ 2 * PowerSeries.mk a)
      - C r1 * X - C r2 * X ^ 2 - C r3 * X ^ 3 - C r4 * X ^ 4 := by
  ring

lemma coeff_rhs_big (a : ℕ → ℚ) (l1 l2 r1 r2 r3 r4 : ℚ) (n : ℕ) :
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

lemma coeff_rhs_small (a : ℕ → ℚ) (l1 l2 r1 r2 r3 r4 : ℚ) (h0 : a 0 = 0) :
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


lemma sum_Icc_one (f : ℕ → ℚ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, f k = ∑ k ∈ Finset.range m, f (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The recurrence satisfied by every sequence with a(n) = Sum_{k=1..n-1} a(k) a(n-k) for n >= 5. -/
theorem conv_rec2 (a : ℕ → ℚ)
    (hrec : ∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) (N : ℕ) :
    ((N : ℚ) + 6) * a (N + 6) - 2 * a 1 * (2 * (N : ℚ) + 9) * a (N + 5)
      - 4 * (a 2 - a 1 ^ 2) * ((N : ℚ) + 3) * a (N + 4)
      - 2 * (a 3 - 2 * a 1 * a 2) * (2 * (N : ℚ) + 3) * a (N + 3)
      - 4 * (a 4 - 2 * a 1 * a 3 - a 2 ^ 2) * (N : ℚ) * a (N + 2) = 0 := by
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, b = fun n => if n = 0 then 0 else a n := ⟨_, rfl⟩
  have hb0 : b 0 = 0 := by simp [hb]
  have hbn : ∀ m : ℕ, m ≠ 0 → b m = a m := fun m hm => by simp [hb, hm]
  have hE : (PowerSeries.mk b) ^ 2 = (1 + C (0 : ℚ) * X + C (0 : ℚ) * X ^ 2) * PowerSeries.mk b
      - (C (a 1) * X + C (a 2 - a 1 ^ 2) * X ^ 2 + C (a 3 - 2 * a 1 * a 2) * X ^ 3
        + C (a 4 - 2 * a 1 * a 3 - a 2 ^ 2) * X ^ 4) := by
    obtain ⟨c0, c1, c2, c3, c4⟩ := coeff_rhs_small b 0 0 (a 1) (a 2 - a 1 ^ 2) (a 3 - 2 * a 1 * a 2)
      (a 4 - 2 * a 1 * a 3 - a 2 ^ 2) hb0
    ext n
    rcases n with _ | _ | _ | _ | _ | n
    · rw [c0, coeff_sq_zero b hb0]
    · rw [c1, coeff_sq_one b hb0, hbn 1 (by omega)]
      ring
    · rw [c2, coeff_sq b hb0 0]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [hbn 1 (by omega), hbn 2 (by omega)]
      ring
    · rw [c3, coeff_sq b hb0 1]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      norm_num
      rw [hbn 1 (by omega), hbn 2 (by omega), hbn 3 (by omega)]
      ring
    · rw [c4, coeff_sq b hb0 2]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      norm_num
      rw [hbn 1 (by omega), hbn 2 (by omega), hbn 3 (by omega), hbn 4 (by omega)]
      ring
    · rw [coeff_rhs_big, show n + 5 = n + 3 + 2 from rfl, coeff_sq b hb0 (n + 3)]
      have h := hrec (n + 5) (by omega)
      rw [show n + 5 - 1 = n + 3 + 1 by omega, sum_Icc_one] at h
      have e3 : ∑ k ∈ Finset.range (n + 3 + 1), b (k + 1) * b (n + 3 + 1 - k)
          = ∑ k ∈ Finset.range (n + 3 + 1), a (k + 1) * a (n + 5 - (k + 1)) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        rw [hbn (k + 1) (by omega), hbn (n + 3 + 1 - k) (by omega),
          show n + 3 + 1 - k = n + 5 - (k + 1) by omega]
      rw [e3, ← h, hbn (n + 3 + 2) (by omega)]
      rw [show n + 3 + 2 = n + 5 from rfl]
      ring
  have h := rec_of_quadratic b 0 0 (a 1) (a 2 - a 1 ^ 2) (a 3 - 2 * a 1 * a 2)
    (a 4 - 2 * a 1 * a 3 - a 2 ^ 2) hE N
  rw [hbn (N + 6) (by omega), hbn (N + 5) (by omega), hbn (N + 4) (by omega), hbn (N + 3) (by omega),
    hbn (N + 2) (by omega)] at h
  linear_combination h

/-- The same recurrence at n = 5. -/
theorem conv_rec2_five (a : ℕ → ℚ)
    (hrec : ∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) :
    5 * a 5 - 2 * a 1 * 7 * a 4 - 4 * (a 2 - a 1 ^ 2) * 2 * a 3
      - 2 * (a 3 - 2 * a 1 * a 2) * 1 * a 2
      - 4 * (a 4 - 2 * a 1 * a 3 - a 2 ^ 2) * (-1) * a 1 = 0 := by
  have h5 := hrec 5 (by norm_num)
  rw [show 5 - 1 = 4 from rfl, sum_Icc_one] at h5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h5
  norm_num at h5
  rw [h5]
  ring

end OMA.QC025275

theorem OMA.solution : type_of% @OMA.S_oeis_a025275.main := by
  intro a h1 h2 h3 h4 hrec n hn
  rcases Nat.lt_or_ge n 6 with hlt | hge
  · have hn5 : n = 5 := by omega
    subst hn5
    have h := OMA.QC025275.conv_rec2_five a hrec
    rw [h1, h2, h3, h4] at h
    norm_num
    rw [h1, h2, h3, h4]
    linear_combination h
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 6 := ⟨n - 6, by omega⟩
    have h := OMA.QC025275.conv_rec2 a hrec N
    rw [h1, h2, h3, h4] at h
    have e1 : N + 6 - 1 = N + 5 := by omega
    have e2 : N + 6 - 2 = N + 4 := by omega
    have e3 : N + 6 - 3 = N + 3 := by omega
    have e4 : N + 6 - 4 = N + 2 := by omega
    simp only [e1, e2, e3, e4]
    push_cast
    linear_combination h
