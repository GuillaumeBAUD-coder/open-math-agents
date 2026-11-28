import OMAStatements.S_oeis_a341249
import Mathlib

open OMA.S_oeis_a341249

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a341249.main) := by
  intro h
  have h2 := (h 2 (by norm_num)).2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlo : (1.4 : ℝ) < Real.sqrt 2 := by nlinarith
  have hhi : Real.sqrt 2 < 1.5 := by nlinarith
  have f1 : ⌊s * ((2 : ℕ) : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    simp only [s]
    push_cast
    constructor <;> nlinarith
  have f2 : a 2 = 6 := by
    unfold a
    rw [f1, Int.floor_eq_iff]
    simp only [r]
    push_cast
    constructor <;> nlinarith
  rw [f2] at h2
  simp only [r, s] at h2
  push_cast at h2
  nlinarith
