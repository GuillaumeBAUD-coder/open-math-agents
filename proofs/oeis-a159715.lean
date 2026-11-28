import OMAStatements.S_oeis_a159715
import Mathlib

namespace OMA.S_oeis_a159715
open PowerSeries

lemma rec3 (n : ℕ) : a (n + 4) = 6 * a (n + 3) - 9 * a (n + 2) := by
  simp only [a]
  have h1 : ¬ (n + 4 < 2) := by omega
  have h2 : ¬ (n + 3 < 2) := by omega
  have h3 : ¬ (n + 2 < 2) := by omega
  simp only [h1, h2, h3, if_false]
  have e1 : n + 4 - 2 = n + 2 := by omega
  have e2 : n + 3 - 2 = n + 1 := by omega
  have e3 : n + 2 - 2 = n := by omega
  rw [e1, e2, e3]
  push_cast
  ring

theorem sol : type_of% @main := by
  refine ⟨?_, ?_, ?_⟩
  · ext n
    have hr : (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 3 * X : PowerSeries ℚ) ^ 2) =
        PowerSeries.mk (fun n => (a n : ℚ)) - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
          + C (9 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) := by
      simp only [map_ofNat]; ring
    have hrhs : (2 * X ^ 2 * (2 - 3 * X) : PowerSeries ℚ) = C (4 : ℚ) * X ^ 2 - C (6 : ℚ) * X ^ 3 := by
      simp only [map_ofNat]; ring
    rw [hr, hrhs]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
    rcases n with _ | _ | _ | _ | n
    · simp [a]
    · simp [a]
    · simp [a]
    · norm_num [a]
    · have h := rec3 n
      have h' : ((a (n + 4) : ℤ) : ℚ) = ((6 * a (n + 3) - 9 * a (n + 2) : ℤ) : ℚ) := by rw [h]
      push_cast at h'
      simp only [show 2 ≤ n + 4 by omega, show 1 ≤ n + 4 by omega, show 3 ≤ n + 4 by omega,
        show ¬ (n + 4 < 2) from by omega, if_true, show n + 4 - 1 = n + 3 by omega,
        show n + 4 - 2 = n + 2 by omega, show ¬ (n + 4 = 2) from by omega,
        show ¬ (n + 4 = 3) from by omega]
      simp
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp [a]
    ring_nf
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have := rec3 m
    simpa using this

end OMA.S_oeis_a159715

theorem OMA.solution : type_of% @OMA.S_oeis_a159715.main := OMA.S_oeis_a159715.sol
