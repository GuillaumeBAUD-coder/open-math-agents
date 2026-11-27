import OMAReductions.R_OeisA217785_conjecture_3_R1

/-! Translation by one makes the polynomial Eisenstein at n + 2. -/

open Polynomial Finset

namespace OMA.WeightedGeometric

lemma weighted_choose_sum (n j : ℕ) :
    (∑ k ∈ range (n + 1), (k + 1) * k.choose j) =
      (j + 1) * (n + 2).choose (j + 2) := by
  induction n with
  | zero =>
    by_cases hj : j = 0
    · subst j; decide
    · have hjpos : 0 < j := by omega
      simp [Nat.choose_eq_zero_of_lt hjpos,
        Nat.choose_eq_zero_of_lt (show 2 < j + 2 by omega)]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hmul := Nat.add_one_mul_choose_eq (n + 1) j
    have hpascal := Nat.choose_succ_succ (n + 2) (j + 1)
    nlinarith

noncomputable def shifted (n : ℕ) : ℤ[X] := taylor 1 (OeisA217785.polyS n)

lemma coeff_shifted (n j : ℕ) :
    (shifted n).coeff j = (((j + 1) * (n + 2).choose (j + 2) : ℕ) : ℤ) := by
  classical
  simp only [shifted, OeisA217785.polyS, map_sum, taylor_apply, mul_comp,
    C_comp, pow_comp, X_comp, C_1, finsetSum_coeff, coeff_C_mul, coeff_X_add_one_pow]
  exact_mod_cast weighted_choose_sum n j

lemma coeff_polyS (n j : ℕ) :
    (OeisA217785.polyS n).coeff j = if j ≤ n then (j + 1 : ℤ) else 0 := by
  classical
  simp only [OeisA217785.polyS, finsetSum_coeff, coeff_C_mul, coeff_X_pow,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

lemma degree_polyS (n : ℕ) : (OeisA217785.polyS n).natDegree = n := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp [coeff_polyS, not_le.mpr hj]
  · apply le_natDegree_of_ne_zero
    simp only [coeff_polyS, if_pos (le_refl n)]
    omega

lemma degree_shifted (n : ℕ) : (shifted n).natDegree = n := by
  rw [shifted, natDegree_taylor, degree_polyS]

lemma leading_shifted (n : ℕ) : (shifted n).leadingCoeff = n + 1 := by
  rw [shifted, leadingCoeff_taylor, leadingCoeff, degree_polyS, coeff_polyS, if_pos (le_refl n)]

lemma eval_shifted (n : ℕ) : (shifted n).eval (-1) = 1 := by
  simp only [shifted, taylor_apply, eval_comp, eval_add, eval_X, eval_C, neg_add_cancel]
  rw [← coeff_zero_eq_eval_zero, coeff_polyS]
  simp

lemma primitive_shifted (n : ℕ) : (shifted n).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro r hr
  apply isUnit_of_dvd_one
  have hd := map_dvd (Polynomial.evalRingHom (-1)) hr
  change (C r).eval (-1) ∣ (shifted n).eval (-1) at hd
  simpa only [eval_C, eval_shifted] using hd

lemma primitive_polyS (n : ℕ) : (OeisA217785.polyS n).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro r hr
  apply isUnit_of_dvd_one
  simpa only [coeff_polyS, Nat.zero_le, if_pos, Nat.cast_zero, zero_add] using
    (C_dvd_iff_dvd_coeff r (OeisA217785.polyS n)).mp hr 0

set_option maxHeartbeats 1000000 in
lemma shifted_irreducible (n : ℕ) (hn : 1 ≤ n) (hp : (n + 2).Prime) :
    Irreducible (shifted n) := by
  let I : Ideal ℤ := Ideal.span {((n + 2 : ℕ) : ℤ)}
  have hpZ : Prime ((n + 2 : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hI : I.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have heis : (shifted n).IsEisensteinAt I := by
    refine ⟨?_, ?_, ?_⟩
    · change (shifted n).leadingCoeff ∉ Ideal.span {((n + 2 : ℕ) : ℤ)}
      rw [leading_shifted, Ideal.mem_span_singleton]
      intro hd
      have hdN : n + 2 ∣ n + 1 := by exact_mod_cast hd
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdN
    · intro j hj
      rw [degree_shifted] at hj
      change (shifted n).coeff j ∈ Ideal.span {((n + 2 : ℕ) : ℤ)}
      rw [coeff_shifted, Ideal.mem_span_singleton]
      have hd : n + 2 ∣ (n + 2).choose (j + 2) :=
        hp.dvd_choose (by omega) (by omega) (le_refl (n + 2))
      exact_mod_cast dvd_mul_of_dvd_right hd (j + 1)
    · change (shifted n).coeff 0 ∉ (Ideal.span {((n + 2 : ℕ) : ℤ)}) ^ 2
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, coeff_shifted]
      simp only [Nat.zero_add, Nat.one_mul]
      intro hd
      have hdN : (n + 2) ^ 2 ∣ (n + 2).choose 2 := by exact_mod_cast hd
      have hpos : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
      have hlt : (n + 2).choose 2 < (n + 2) ^ 2 := by
        rw [Nat.choose_two_right]
        apply lt_of_le_of_lt (Nat.div_le_self _ _)
        have hs : n + 2 - 1 + 1 = n + 2 := by omega
        nlinarith
      exact Nat.not_dvd_of_pos_of_lt hpos hlt hdN
  exact heis.irreducible hI (primitive_shifted n) (by rw [degree_shifted]; omega)

end OMA.WeightedGeometric

-- Step OeisA217785.conjecture_3.R1.H1: hypothesis H1 of reduction OeisA217785.conjecture_3.R1
-- Credit: @DeepDuke
-- H1 := ∀ n : ℕ, 1 ≤ n → (n + 2).Prime →   Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n))

theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1.H1 := by
  intro n hn hp
  have hiZ : Irreducible (OeisA217785.polyS n) :=
    (MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ))).mp
      (OMA.WeightedGeometric.shifted_irreducible n hn hp)
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (OMA.WeightedGeometric.primitive_polyS n)).mp hiZ

