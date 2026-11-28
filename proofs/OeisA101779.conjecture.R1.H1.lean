import OMAReductions.R_OeisA101779_conjecture_R1
import Mathlib

/-! `k = 2894219` makes `i * k + (i - 1)` prime for every `i = 1, …, 8`, so it is a witness for
`n = 8`, and (restricting `i`) also for `n = 6` and `n = 7`. Each of the eight primes is certified
by `norm_num`. -/

namespace OMA.Step_OeisA101779_conjecture_R1_H1

open OeisA101779

theorem ak_eight : Ak 8 2894219 := by
  intro i hi1 hi8
  interval_cases i <;> norm_num

end OMA.Step_OeisA101779_conjecture_R1_H1

theorem OMA.solution : OMA.R_OeisA101779_conjecture_R1.H1 := by
  intro n hn6 hn8
  exact ⟨2894219, fun i hi1 hin =>
    OMA.Step_OeisA101779_conjecture_R1_H1.ak_eight i hi1 (le_trans hin hn8)⟩
