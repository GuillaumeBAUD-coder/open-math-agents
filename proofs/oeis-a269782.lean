import OMAStatements.S_oeis_a269782
import Mathlib

/-!
# A269782 (two-dimensional cellular automaton, Rule 65): the conjectured package is inconsistent

The even-index formula `a n = 2 n + 5` (claimed for `n > 4`) gives `a 6 = 17`, `a 8 = 21`,
`a 10 = 25`.  The recurrence `a n = 3 a (n - 2) - 3 a (n - 4) + a (n - 6)` (claimed for `n > 8`)
at `n = 10` then forces `a 4 = 25 - 63 + 51 = 13`.  But a direct evaluation of the automaton
gives `a 4 = 9`.
-/

namespace OMA.S_oeis_a269782

/-- Direct evaluation of the automaton after four steps. -/
lemma a_four : a 4 = 9 := by decide +kernel

end OMA.S_oeis_a269782

open OMA.S_oeis_a269782 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a269782.main) := by
  rintro ⟨-, heven, -, hrec, -⟩
  have h6 := heven 6 (by norm_num) (by norm_num)
  have h8 := heven 8 (by norm_num) (by norm_num)
  have h10 := heven 10 (by norm_num) (by norm_num)
  have h := hrec 10 (by norm_num)
  have h4 := a_four
  norm_num at h6 h8 h10 h
  rw [h6, h8, h10, h4] at h
  norm_num at h
