import OMAStatements.S_oeis_a270086

open OMA.S_oeis_a270086 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X) ^ 3) =
      3 + 4 * X + 26 * X ^ 2 - 4 * X ^ 3 - X ^ 4 + 4 * X ^ 5 + 4 * X ^ 6 - 8 * X ^ 7 + 4 * X ^ 9)
    (hrule : ∀ n : ℕ, 7 < n → a n = -a (n - 1) + 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) - a (n - 5)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (1 : ℤ) • (mk a * X ^ 1)
      + (-2 : ℤ) • (mk a * X ^ 2)
      + (-2 : ℤ) • (mk a * X ^ 3)
      + (1 : ℤ) • (mk a * X ^ 4)
      + (1 : ℤ) • (mk a * X ^ 5) =
      (3 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (26 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (-4 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (-1 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 6 : PowerSeries ℤ)
      + (-8 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 9 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 9) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 9 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270086.main) := by
  intro h
  exact coefficient_contradiction a h.2.2.2.2 h.2.2.2.1
