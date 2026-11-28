import OMAStatements.S_oeis_a210376
import Mathlib

open OMA.S_oeis_a210376
open PowerSeries

namespace P210376

set_option maxRecDepth 100000 in
theorem vals : a 2 = 10 ∧ a 3 = 40 ∧ a 4 = 85 ∧ a 5 = 140 ∧ a 6 = 206 := by
  decide +kernel

end P210376

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a210376.main) := by
  rintro ⟨-, -, h⟩
  have h6 := h 6 (by norm_num)
  obtain ⟨v2, v3, v4, v5, v6⟩ := P210376.vals
  norm_num [v2, v3, v4, v5, v6] at h6
