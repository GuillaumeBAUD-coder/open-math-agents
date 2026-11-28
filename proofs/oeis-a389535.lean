import OMAStatements.S_oeis_a389535
import Mathlib

/-! A389535, conjecture (7): `A(x)^5 ≡ A(x^5) (mod 5)`.
This holds for every power series with integer coefficients: modulo 5 the fifth power map
is the Frobenius endomorphism, which sends a series to its expansion by 5 with every
coefficient raised to the fifth power, and `c^5 = c` in `ZMod 5`. -/

namespace OMA.Helpers

theorem a389535_fifth_power_mod5 (B : PowerSeries (ZMod 5)) (n : ℕ) :
    PowerSeries.coeff n (B ^ 5) =
      (if 5 ∣ n then PowerSeries.coeff (n / 5) B else 0) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : (5 : ℕ) ≠ 0 := by norm_num
  have key : PowerSeries.map (frobenius (ZMod 5) 5) (PowerSeries.expand 5 h5 B) = B ^ 5 :=
    MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 5) 5 h5 (f := B)
  rw [← key, ZMod.frobenius_zmod, PowerSeries.coeff_map, PowerSeries.coeff_expand]
  rfl

theorem a389535_coeff_mod5 (A : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (A ^ 5) ≡
        (if 5 ∣ n then PowerSeries.coeff (n / 5) A else 0) [ZMOD 5] := by
  have h := a389535_fifth_power_mod5 (PowerSeries.map (Int.castRingHom (ZMod 5)) A) n
  rw [← map_pow, PowerSeries.coeff_map, PowerSeries.coeff_map] at h
  have h' : ((PowerSeries.coeff n (A ^ 5) : ℤ) : ZMod 5) =
      (((if 5 ∣ n then PowerSeries.coeff (n / 5) A else 0 : ℤ)) : ZMod 5) := by
    simp only [eq_intCast] at h
    rw [h]
    split_ifs <;> simp
  exact (ZMod.intCast_eq_intCast_iff _ _ 5).mp h'

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a389535.main := by
  intro A _ n
  exact OMA.Helpers.a389535_coeff_mod5 A n
