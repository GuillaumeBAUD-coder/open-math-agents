import OMAStatements.S_oeis_a394981
import Mathlib

namespace OMA.S_oeis_a394981

theorem c1 : count 1 = 1 := by decide +kernel
theorem c2 : count 2 = 1 := by decide +kernel

end OMA.S_oeis_a394981

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a394981.main) := by
  intro h
  have := h 1 (by norm_num) (by norm_num)
  have h2 : OMA.S_oeis_a394981.count (1+1) = 1 := OMA.S_oeis_a394981.c2
  rw [h2, OMA.S_oeis_a394981.c1] at this
  omega
