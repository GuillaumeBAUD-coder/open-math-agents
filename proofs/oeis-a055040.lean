import OMAStatements.S_oeis_a055040

namespace OMA.P_oeis_a055040

open OMA.S_oeis_a055040

lemma six_le_of_isTerm {m : ℕ} (hm : IsTerm m) : 6 ≤ m := by
  obtain ⟨i, j, rfl⟩ := hm
  have h1 : 3 ≤ 3 ^ (2 * i + 1) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (2 * i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ≤ 3 * j + 2 := by omega
  calc 6 = 3 * 2 := by norm_num
    _ ≤ 3 ^ (2 * i + 1) * (3 * j + 2) := Nat.mul_le_mul h1 h2

lemma a_one_ge : 6 ≤ a 1 := by
  unfold a
  rw [show 1 - 1 = 0 from rfl, Nat.nth_zero]
  have hne : {m | IsTerm m}.Nonempty := ⟨6, 0, 0, by norm_num⟩
  exact six_le_of_isTerm (Nat.sInf_mem hne)

lemma coeff_one_lhs (D : PowerSeries ℤ) (hD : PowerSeries.constantCoeff D = 1) :
    PowerSeries.coeff 1 (A * D) = (a 1 : ℤ) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [A, hD]

end OMA.P_oeis_a055040

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a055040.main) := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  rw [OMA.P_oeis_a055040.coeff_one_lhs _ (by simp)] at h1
  have h6 := OMA.P_oeis_a055040.a_one_ge
  have hr : PowerSeries.coeff 1 ((PowerSeries.X : PowerSeries ℤ) * (PowerSeries.X + 2) *
      (PowerSeries.X ^ 2 + PowerSeries.X + 1) * (PowerSeries.X ^ 7 + PowerSeries.X ^ 3 + 1)) = 2 := by
    rw [mul_assoc, mul_assoc, PowerSeries.coeff_succ_X_mul]
    simp
    exact map_ofNat PowerSeries.constantCoeff 2
  rw [hr] at h1
  omega
