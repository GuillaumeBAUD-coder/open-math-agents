import OMAStatements.S_oeis_a210377
import Mathlib

open OMA.S_oeis_a210377
open PowerSeries

namespace P210377

set_option maxRecDepth 100000 in
theorem vals : a 3 = 31 ∧ a 4 = 80 ∧ a 5 = 146 ∧ a 6 = 224 ∧ a 7 = 315 := by
  decide +kernel

end P210377

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a210377.main) := by
  rintro ⟨-, -, h⟩
  have h7 := h 7 (by norm_num)
  obtain ⟨v3, v4, v5, v6, v7⟩ := P210377.vals
  norm_num [v3, v4, v5, v6, v7] at h7
