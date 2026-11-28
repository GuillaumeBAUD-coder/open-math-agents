import OMAStatements.S_oeis_a378840
import Mathlib

namespace OMA.S_oeis_a378840
open PowerSeries

theorem sol : type_of% @main := by
  intro A C B hA hC0 hA2 hB
  obtain ⟨D, hD⟩ : ∃ D : PowerSeries ℚ, D = 1 + X * C ^ 4 * (1 + C) := ⟨_, rfl⟩
  rw [← hD] at hA2
  have hD0 : constantCoeff D = 1 := by simp [hD]
  have hC0' : constantCoeff C = 1 := by simpa using hC0
  have hcube : C ^ 3 = D ^ 3 := by rw [← hA, hA2]
  have hCD : C = D := by
    have h : (C - D) * (C ^ 2 + C * D + D ^ 2) = 0 := by
      have : C ^ 3 - D ^ 3 = 0 := sub_eq_zero.mpr hcube
      linear_combination this
    have hne : C ^ 2 + C * D + D ^ 2 ≠ 0 := by
      intro h0
      have := congrArg constantCoeff h0
      norm_num [hC0', hD0] at this
    rcases mul_eq_zero.mp h with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hne
  have hCeq : C = 1 + X * C ^ 4 + X * C ^ 5 := by
    have e : D = 1 + X * C ^ 4 + X * C ^ 5 := by rw [hD]; ring
    exact hCD.trans e
  have hdiv : ∀ n : ℕ, (X : PowerSeries ℚ) ^ n ∣ B - C := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : B - C = X * ((B ^ 4 - C ^ 4) + (B ^ 5 - C ^ 5)) := by
        have e1 : B - C = (1 + X * B ^ 4 + X * B ^ 5) - (1 + X * C ^ 4 + X * C ^ 5) := by
          rw [← hB, ← hCeq]
        rw [e1]; ring
      have h2 : X ^ n ∣ (B ^ 4 - C ^ 4) + (B ^ 5 - C ^ 5) :=
        dvd_add (dvd_trans ih (sub_dvd_pow_sub_pow B C 4 |> fun h => by exact h))
          (dvd_trans ih (sub_dvd_pow_sub_pow B C 5))
      rw [h1]
      have : (X : PowerSeries ℚ) ^ (n + 1) = X * X ^ n := by ring
      rw [this]
      exact mul_dvd_mul_left X h2
  have hBC : B = C := by
    ext n
    have := (PowerSeries.X_pow_dvd_iff (n := n + 1) (φ := B - C)).mp (hdiv (n + 1)) n (by omega)
    simpa [sub_eq_zero] using this
  rw [hA, hBC]

end OMA.S_oeis_a378840

theorem OMA.solution : type_of% @OMA.S_oeis_a378840.main := OMA.S_oeis_a378840.sol
