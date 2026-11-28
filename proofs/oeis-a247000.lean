import OMAStatements.S_oeis_a247000
import Mathlib

open OMA.S_oeis_a247000
open PowerSeries

namespace P247000

set_option maxRecDepth 100000 in
theorem v3 : a 3 = 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem v4 : a 4 = 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem v6 : a 6 = 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem v7 : a 7 = 10 := by decide +kernel

end P247000

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a247000.main) := by
  rintro ⟨h, -⟩
  have h7 := h 7 (by norm_num)
  norm_num [P247000.v7, P247000.v6, P247000.v4, P247000.v3] at h7
