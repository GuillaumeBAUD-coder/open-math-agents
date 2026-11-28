import OMAStatements.S_oeis_a270085
import Mathlib

/-!
# A270085 (partial sums for the Rule 65 automaton): the conjectured package is inconsistent

The closed forms (claimed for `n > 3`) give
`a 4, …, a 10 = 55, 151, 168, 356, 377, 689, 714`.  The recurrence (claimed for `n > 8`) at
`n = 10` reads `714 = 689 + 3·377 - 3·356 - 3·168 + 3·151 + 55 - a 3`, which forces `a 3 = 42`.
But a direct evaluation of the automaton gives `a 3 = 46`.
-/

namespace OMA.S_oeis_a270085

/-- Direct evaluation of the first four generations. -/
lemma a_three : a 3 = 46 := by decide +kernel

end OMA.S_oeis_a270085

open OMA.S_oeis_a270085 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270085.main) := by
  rintro ⟨-, heven, hodd, hrec, -⟩
  have h4 := heven 4 (by norm_num) (by norm_num)
  have h5 := hodd 5 (by norm_num) (by norm_num)
  have h6 := heven 6 (by norm_num) (by norm_num)
  have h7 := hodd 7 (by norm_num) (by norm_num)
  have h8 := heven 8 (by norm_num) (by norm_num)
  have h9 := hodd 9 (by norm_num) (by norm_num)
  have h10 := heven 10 (by norm_num) (by norm_num)
  have h : (a 10 : ℚ) = a 9 + 3 * a 8 - 3 * a 7 - 3 * a 6 + 3 * a 5 + a 4 - a 3 := by
    exact_mod_cast hrec 10 (by norm_num)
  rw [h4, h5, h6, h7, h8, h9, h10, a_three] at h
  norm_num at h
