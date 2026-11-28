import OMAStatements.S_oeis_a176610

-- Problem: A176610 (OEIS), conjecture of R. J. Mathar: P-recursive recurrence for n >= 5.
-- Credit: @AngelHS12
-- Proof: F = sum a(n) x^n satisfies (1-x)^2 (F - 1 + x - x F^2) = x^2 (3 - 2x). With B = 1 - 2xF this
-- gives (1-x)^2 B^2 = 1 - 6x + 13x^2 - 24x^3 + 12x^4. Differentiating, eliminating B^2 and cancelling
-- 4(1-x) yields (1 - 5x + 9x^2 - x^3) F + x (1-x)(1 - 6x + 13x^2 - 24x^3 + 12x^4) dF/dx
-- = 1 - 5x + 18x^2 - 18x^3 + 6x^4, whose coefficient of x^n (n >= 5) is the conjectured recurrence.

open PowerSeries

namespace OMAProof176610

open OMA.S_oeis_a176610

lemma aList_succ (n : ℕ) : ∃ x, aList (n + 1) = aList n ++ [x] := by
  cases n with
  | zero => exact ⟨0, rfl⟩
  | succ m => exact ⟨_, rfl⟩

lemma aList_length (n : ℕ) : (aList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨x, hx⟩ := aList_succ n
    simp [hx, ih]

lemma getD_aList (n k : ℕ) (hk : k ≤ n) : (aList n).getD k 0 = a k := by
  induction n with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · obtain ⟨x, hx⟩ := aList_succ n
      rw [hx, List.getD_append _ _ _ _ (by rw [aList_length]; exact h)]
      exact ih (by omega)
    · obtain rfl : k = n + 1 := by omega
      rfl

lemma a_rec (n : ℕ) :
    a (n + 2) = (∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p)) + ((n : ℤ) + 2) + 1 := by
  have h2 : aList (n + 2) = aList (n + 1) ++
      [(∑ p ∈ Finset.range (n + 2),
        (aList (n + 1)).getD p 0 * (aList (n + 1)).getD (n + 1 - p) 0) + ((n : ℤ) + 2) + 1] :=
    rfl
  have h1 : a (n + 2) = (aList (n + 2)).getD (n + 2) 0 := rfl
  rw [h1, h2, List.getD_append_right _ _ _ _ (by rw [aList_length])]
  simp only [aList_length, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_range] at hp
  rw [getD_aList _ _ (by omega), getD_aList _ _ (by omega)]

lemma a_zero : a 0 = 1 := rfl

lemma a_one : a 1 = 0 := rfl

lemma coeff_sq (n : ℕ) :
    coeff (n + 1) ((mk a) ^ 2) = ∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [coeff_mk]

lemma key_G : mk a - 1 + X - X * (mk a) ^ 2 = X ^ 2 * mk (fun n : ℕ => (n : ℤ) + 3) := by
  ext n
  rcases n with _ | _ | n
  · simp [coeff_X_pow_mul', a_zero]
  · have h1 : coeff 1 (X * (mk a) ^ 2) = 1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, pow_two, coeff_mul]
      simp [a_zero]
    simp only [map_sub, map_add, coeff_mk, coeff_one, coeff_X, coeff_X_pow_mul', h1]
    norm_num [a_one]
  · rw [show n + 1 + 1 = n + 2 from rfl]
    simp only [map_sub, map_add, coeff_mk, coeff_one, coeff_X, coeff_succ_X_mul,
      coeff_sq, coeff_X_pow_mul', a_rec]
    simp
    ring

lemma geoC : mk (fun n : ℕ => (n : ℤ) + 3)
    - C (2 : ℤ) * (X ^ 1 * mk (fun n : ℕ => (n : ℤ) + 3))
    + X ^ 2 * mk (fun n : ℕ => (n : ℤ) + 3) = C (3 : ℤ) - C (2 : ℤ) * X ^ 1 := by
  ext k
  rcases k with _ | _ | k
  · simp only [map_add, map_sub, coeff_mk, coeff_C_mul, coeff_C, coeff_X_pow_mul', coeff_X_pow]
    norm_num
  · simp only [map_add, map_sub, coeff_mk, coeff_C_mul, coeff_C, coeff_X_pow_mul', coeff_X_pow]
    norm_num
  · simp only [map_add, map_sub, coeff_mk, coeff_C_mul, coeff_C, coeff_X_pow_mul', coeff_X_pow]
    simp
    push_cast
    ring

lemma geo : (1 - X) ^ 2 * mk (fun n : ℕ => (n : ℤ) + 3) = (3 - 2 * X : ℤ⟦X⟧) := by
  have h := geoC
  simp only [map_ofNat] at h
  linear_combination h

lemma E1 : (1 - X) ^ 2 * (mk a - 1 + X - X * (mk a) ^ 2) = (X ^ 2 * (3 - 2 * X) : ℤ⟦X⟧) := by
  rw [key_G]
  linear_combination X ^ 2 * geo

lemma E2 : (1 - X) ^ 2 * (1 - 2 * X * mk a) ^ 2 =
    (1 - 6 * X + 13 * X ^ 2 - 24 * X ^ 3 + 12 * X ^ 4 : ℤ⟦X⟧) := by
  linear_combination (-4 * X) * E1

lemma E2C : (1 - X) ^ 2 * (1 - C (2 : ℤ) * X * mk a) ^ 2 =
    (1 - C (6 : ℤ) * X + C (13 : ℤ) * X ^ 2 - C (24 : ℤ) * X ^ 3 + C (12 : ℤ) * X ^ 4 : ℤ⟦X⟧) := by
  simp only [map_ofNat]
  exact E2

lemma E3 : d⁄dX ℤ ((1 - X) ^ 2 * (1 - C (2 : ℤ) * X * mk a) ^ 2) =
    d⁄dX ℤ (1 - C (6 : ℤ) * X + C (13 : ℤ) * X ^ 2 - C (24 : ℤ) * X ^ 3
      + C (12 : ℤ) * X ^ 4 : ℤ⟦X⟧) :=
  congrArg _ E2C

lemma E3' : (-2 + 2 * X) * (1 - 2 * X * mk a) ^ 2
      + (1 - X) ^ 2 * (2 * ((1 - 2 * X * mk a) * (-(2 * X * d⁄dX ℤ (mk a)) - 2 * mk a)))
      = (-6 + 26 * X - 72 * X ^ 2 + 48 * X ^ 3 : ℤ⟦X⟧) := by
  have h := E3
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, derivative_C,
    derivative_X, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub] at h
  simp only [map_ofNat, Nat.cast_ofNat] at h
  linear_combination h

lemma T4 : (4 * (1 - X) : ℤ⟦X⟧) * ((1 - 5 * X + 9 * X ^ 2 - X ^ 3) * mk a
    + X * ((1 - X) * (1 - 6 * X + 13 * X ^ 2 - 24 * X ^ 3 + 12 * X ^ 4)) * d⁄dX ℤ (mk a)
    - (1 - 5 * X + 18 * X ^ 2 - 18 * X ^ 3 + 6 * X ^ 4)) = 0 := by
  linear_combination
    (2 * (1 - X) ^ 2 * (-(2 * X * d⁄dX ℤ (mk a)) - 2 * mk a)
      + (-2 + 2 * X) * (1 - 2 * X * mk a)) * E2
    + (-((1 - X) ^ 2 * (1 - 2 * X * mk a))) * E3'

lemma T1 : (1 - 5 * X + 9 * X ^ 2 - X ^ 3) * mk a
    + X * ((1 - X) * (1 - 6 * X + 13 * X ^ 2 - 24 * X ^ 3 + 12 * X ^ 4)) * d⁄dX ℤ (mk a)
    = (1 - 5 * X + 18 * X ^ 2 - 18 * X ^ 3 + 6 * X ^ 4 : ℤ⟦X⟧) := by
  have h4 : (4 * (1 - X) : ℤ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    simp only [coeff_zero_eq_constantCoeff_apply, map_mul, map_sub, map_one, constantCoeff_X,
      map_ofNat, map_zero] at this
    norm_num at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp T4).resolve_left h4)

lemma T1C : mk a - C (5 : ℤ) * (X ^ 1 * mk a) + C (9 : ℤ) * (X ^ 2 * mk a) - X ^ 3 * mk a
    + X ^ 1 * d⁄dX ℤ (mk a) - C (7 : ℤ) * (X ^ 2 * d⁄dX ℤ (mk a))
    + C (19 : ℤ) * (X ^ 3 * d⁄dX ℤ (mk a)) - C (37 : ℤ) * (X ^ 4 * d⁄dX ℤ (mk a))
    + C (36 : ℤ) * (X ^ 5 * d⁄dX ℤ (mk a)) - C (12 : ℤ) * (X ^ 6 * d⁄dX ℤ (mk a))
    = 1 - C (5 : ℤ) * X ^ 1 + C (18 : ℤ) * X ^ 2 - C (18 : ℤ) * X ^ 3 + C (6 : ℤ) * X ^ 4 := by
  simp only [map_ofNat]
  linear_combination T1

theorem rec_main (n : ℕ) (hn : 5 ≤ n) :
    ((n : ℤ) + 1) * a n
      + (2 - 7 * (n : ℤ)) * a (n - 1)
      + (19 * (n : ℤ) - 29) * a (n - 2)
      + (110 - 37 * (n : ℤ)) * a (n - 3)
      + 36 * ((n : ℤ) - 4) * a (n - 4)
      + 12 * (5 - (n : ℤ)) * a (n - 5) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hc := congrArg (coeff (k + 5)) T1C
  simp only [map_add, map_sub, coeff_C_mul, coeff_mk, coeff_X_pow_mul', coeff_derivative,
    coeff_one, coeff_X_pow] at hc
  simp at hc
  simp only [show k + 4 + 1 = k + 5 from rfl, show k + 3 + 1 = k + 4 from rfl,
    show k + 2 + 1 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl] at hc
  rw [show k + 5 - 1 = k + 4 from rfl, show k + 5 - 2 = k + 3 from rfl,
    show k + 5 - 3 = k + 2 from rfl, show k + 5 - 4 = k + 1 from rfl,
    show k + 5 - 5 = k from rfl]
  split_ifs at hc with hk
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hc
    push_cast at hc ⊢
    linear_combination hc
  · obtain rfl : k = 0 := by omega
    push_cast at hc ⊢
    linear_combination hc

end OMAProof176610

theorem OMA.solution : type_of% @OMA.S_oeis_a176610.main := by
  intro n hn
  exact OMAProof176610.rec_main n hn
