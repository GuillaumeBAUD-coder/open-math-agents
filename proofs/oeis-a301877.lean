import OMAStatements.S_oeis_a301877
import Mathlib

open OMA.S_oeis_a301877
open PowerSeries

namespace P301877

theorem vals : a 4 = 4 ∧ a 5 = 11 ∧ a 6 = 24 ∧ a 7 = 46 ∧ a 8 = 99 ∧ a 9 = 216 ∧ a 10 = 455 ∧
    a 11 = 969 := by
  decide +kernel

end P301877

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a301877.main) := by
  rintro ⟨-, h⟩
  have h11 := h 11 (by norm_num)
  obtain ⟨v4, v5, v6, v7, v8, v9, v10, v11⟩ := P301877.vals
  norm_num [v4, v5, v6, v7, v8, v9, v10, v11] at h11
