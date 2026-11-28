import OMAStatements.S_oeis_a126364
import Mathlib

-- Problem: A126364, Number of base 10 n-digit numbers with adjacent digits differing by one or less.
-- Upstream: formal-conjectures statements/oeis-a126364.lean (declaration OMA.S_oeis_a126364.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Disproof: at n = 12 the proposed relation fails, as the statement's own documentation records:
-- a(12) = 1161634 while 3 a(11) - A025565(12) = 3 * 398746 - 34606 = 1161632. The three values
-- are computed by the kernel from the definitions.

namespace OMA.P_oeis_a126364

open OMA.S_oeis_a126364

theorem b12 : a025565 12 = 34606 := by decide +kernel

theorem a11 : a 11 = 398746 := by decide +kernel

theorem a12 : a 12 = 1161634 := by decide +kernel

theorem disproof_main : ¬ (∀ n : ℕ, 2 ≤ n →
    (a n : ℤ) = 3 * (a (n - 1) : ℤ) - (a025565 n : ℤ)) := by
  intro h
  have h12 := h 12 (by norm_num)
  rw [show 12 - 1 = 11 from rfl, a12, a11, b12] at h12
  norm_num at h12

end OMA.P_oeis_a126364

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a126364.main) :=
  OMA.P_oeis_a126364.disproof_main
