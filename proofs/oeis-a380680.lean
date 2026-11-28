import OMAStatements.S_oeis_a380680

namespace OMA.S_oeis_a380680

/-!
## Disproof of OEIS A380680

At `n = 1`, `IsSquare 1` holds (`1 = 1 * 1`), yet
`A380680 1 = 2 * (term 1).coeff 1 = 2 * 2 = 4`,
so `A380680 1 % 4 = 0 ≠ 2`.
(More generally, reducing `term m = X^(m^2) * (2 - X^m)^m / (1 - 2*X^m)^m` modulo `2` gives
`X^(2*m^2)`, so `A380680 n % 4 = 2` holds iff `n` is twice a square, e.g. `n = 2, 8, 18, 32, ...`,
not iff `n` is a square.)
-/

private lemma coeff_term_one_one : (term 1).coeff 1 = 2 := by
  have h1 : (invOneSubTwoXpow 1).coeff 0 = 1 := by
    simp [invOneSubTwoXpow]
  have h2 : ((2 - PowerSeries.X ^ 1 : PowerSeries ℤ) ^ 1).coeff 0 = 2 := by
    simp [map_ofNat]
  have hterm : term 1 = PowerSeries.X * ((2 - PowerSeries.X ^ 1) ^ 1 * (invOneSubTwoXpow 1) ^ 1) := by
    simp only [term, one_pow, pow_one, mul_assoc]
  rw [hterm]
  have hmul : PowerSeries.coeff 1 (PowerSeries.X * ((2 - PowerSeries.X ^ 1 : PowerSeries ℤ) ^ 1 * (invOneSubTwoXpow 1) ^ 1)) =
      PowerSeries.coeff 0 ((2 - PowerSeries.X ^ 1 : PowerSeries ℤ) ^ 1 * (invOneSubTwoXpow 1) ^ 1) :=
    PowerSeries.coeff_succ_X_mul 0 _
  rw [hmul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff,
    h2, pow_one, h1]
  norm_num

private lemma A380680_one : A380680 1 = 4 := by
  simp only [A380680, one_ne_zero, ↓reduceIte, zero_add, Finset.Icc_self, Finset.sum_singleton,
    coeff_term_one_one]
  norm_num

private lemma disproof_proof : ¬ (∀ n : ℕ, 1 ≤ n →
    (A380680 n % 4 = 2 ↔ IsSquare n) ∧ (¬ IsSquare n → (4 : ℤ) ∣ A380680 n)) := by
  intro h
  have h1 := (h 1 (le_refl 1)).1
  have hsq : IsSquare (1 : ℕ) := ⟨1, by norm_num⟩
  have hmod := h1.mpr hsq
  rw [A380680_one] at hmod
  norm_num at hmod

end OMA.S_oeis_a380680

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a380680.main) :=
  OMA.S_oeis_a380680.disproof_proof
