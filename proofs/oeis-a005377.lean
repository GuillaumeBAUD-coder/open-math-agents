import OMAStatements.S_oeis_a005377
import Mathlib

namespace OMA.S_oeis_a005377

theorem a_vals : a 31 = 49 ∧ a 30 = 46 ∧ a 29 = 44 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end OMA.S_oeis_a005377

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005377.main) := by
  intro h
  have h2 := congrArg (PowerSeries.coeff 30) h
  obtain ⟨h1, h0, hm⟩ := OMA.S_oeis_a005377.a_vals
  have e : (PowerSeries.X - 1 : PowerSeries ℤ)^2
      = PowerSeries.X^2 - PowerSeries.X - PowerSeries.X + 1 := by ring
  rw [e] at h2
  have c2 : PowerSeries.coeff 30 (OMA.S_oeis_a005377.generating * PowerSeries.X^2) = 44 := by
    rw [PowerSeries.coeff_mul_X_pow']; simp [OMA.S_oeis_a005377.generating, hm]
  have c1 : PowerSeries.coeff 30 (OMA.S_oeis_a005377.generating * PowerSeries.X) = 46 := by
    have := PowerSeries.coeff_mul_X_pow' (OMA.S_oeis_a005377.generating) 1 30
    rw [pow_one] at this
    rw [this]; simp [OMA.S_oeis_a005377.generating, h0]
  have c0 : PowerSeries.coeff 30 OMA.S_oeis_a005377.generating = 49 := by
    simp [OMA.S_oeis_a005377.generating, h1]
  have r : PowerSeries.coeff 30 ((PowerSeries.X:PowerSeries ℤ)^4 * (PowerSeries.X^2+1) * (PowerSeries.X^4-PowerSeries.X^2+1)) = 0 := by
    have : (PowerSeries.X:PowerSeries ℤ)^4 * (PowerSeries.X^2+1) * (PowerSeries.X^4-PowerSeries.X^2+1) = PowerSeries.X^10 + PowerSeries.X^4 := by ring
    rw [this]; simp [PowerSeries.coeff_X_pow]
  have : OMA.S_oeis_a005377.generating * (PowerSeries.X^2 - PowerSeries.X - PowerSeries.X + 1)
      = OMA.S_oeis_a005377.generating * PowerSeries.X^2 - OMA.S_oeis_a005377.generating * PowerSeries.X
        - OMA.S_oeis_a005377.generating * PowerSeries.X + OMA.S_oeis_a005377.generating := by ring
  rw [this] at h2
  simp only [map_add, map_sub, c2, c1, c0, r] at h2
  omega
