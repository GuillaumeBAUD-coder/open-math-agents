import OMAStatements.S_oeis_a126726
import Mathlib

namespace A126726Aux

lemma sc2 : OMA.S_oeis_a126726.squareCount 2 = 0 := by decide

lemma bp2 : OMA.S_oeis_a126726.betweenPowers 2 = 0 := by
  have e1 : Nat.sqrt (2 ^ (2 + 1)) = 2 :=
    (Nat.eq_sqrt'.mpr ⟨by norm_num, by norm_num⟩).symm
  have e2 : Nat.sqrt (2 ^ 2) = 2 :=
    (Nat.eq_sqrt'.mpr ⟨by norm_num, by norm_num⟩).symm
  have e : Nat.sqrt (2 ^ (2 + 1)) = Nat.sqrt (2 ^ 2) := by rw [e1, e2]
  exact Nat.sub_eq_zero_of_le (le_of_eq e)

end A126726Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a126726.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  rw [A126726Aux.sc2, A126726Aux.bp2] at h2
  norm_num at h2
