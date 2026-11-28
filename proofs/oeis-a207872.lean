import OMAStatements.S_oeis_a207872
import Mathlib.Data.Rat.Init
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a207872.main) := by
  intro h
  have := h 2 (by norm_num) [false, true] (by rfl) (by rfl) (by rfl)
  have e1 : (OMA.S_oeis_a207872.atHalf [false, true]) = 1 / 2 := by
    simp [OMA.S_oeis_a207872.atHalf]
  have e2 : OMA.S_oeis_a207872.reversedBinary [false, true] = 1 := by rfl
  rw [e1, e2] at this
  have : (1 / 2 : ℚ).den = 2 := by norm_num [Rat.den_div_eq_of_coprime]
  omega
