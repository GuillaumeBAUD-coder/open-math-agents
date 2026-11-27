import OMAStatements.S_oeis_a101917

-- Problem: OEIS A101917, Ralf Stephan's conjectured generating function
-- (1 + x^7) / (1 + x + x^7) for the expansion of A(x) = 1 / (1 + x A(x^7)).
-- Disproof: the coefficient of x^57 in A(x) (1 + x + x^7) is a(57) + a(56) + a(50) = -1,
-- not 0 (J. W. M. Meijer, OEIS A101917: the conjectured g.f. first differs at a(57)).

namespace OMA.A101917Proof

open OMA.S_oeis_a101917

set_option maxRecDepth 100000 in
lemma coeffs : a 57 + a 56 + a 50 = -1 := by
  decide

lemma coeff57 :
    PowerSeries.coeff 57 (series * (1 + PowerSeries.X + PowerSeries.X ^ 7)) =
      a 57 + a 56 + a 50 := by
  have h1 : series * (1 + PowerSeries.X + PowerSeries.X ^ 7) =
      series + series * PowerSeries.X ^ 1 + series * PowerSeries.X ^ 7 := by ring
  rw [h1, map_add, map_add, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow']
  simp [series]

lemma rhs57 : PowerSeries.coeff 57 ((1 : PowerSeries ℤ) + PowerSeries.X ^ 7) = 0 := by
  rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  simp

end OMA.A101917Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a101917.main) := by
  intro h
  have h57 := congrArg (PowerSeries.coeff 57) h
  rw [OMA.A101917Proof.coeff57, OMA.A101917Proof.rhs57, OMA.A101917Proof.coeffs] at h57
  exact absurd h57 (by norm_num)
