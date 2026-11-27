import OMAStatements.S_oeis_a341249
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a341249.main) := by
  intro h
  have h2 := (h 2 (by norm_num)).2
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by
    have h1 : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at h1
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith
  have f1 : ⌊OMA.S_oeis_a341249.s * ((2 : ℕ) : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    unfold OMA.S_oeis_a341249.s
    push_cast
    constructor <;> linarith
  have f2 : OMA.S_oeis_a341249.a 2 = 6 := by
    unfold OMA.S_oeis_a341249.a
    rw [f1, Int.floor_eq_iff]
    unfold OMA.S_oeis_a341249.r
    push_cast
    constructor <;> linarith
  rw [f2] at h2
  unfold OMA.S_oeis_a341249.r OMA.S_oeis_a341249.s at h2
  push_cast at h2
  nlinarith
