import OMAStatements.S_oeis_a008544
import Mathlib

/-! Proof for OEIS A008544: unfold the products with `a (n+1) = a n · (3n+2)` and compare
polynomial expressions. Credit: Sudharsan Rajendiran -/

theorem OMA.solution : type_of% @OMA.S_oeis_a008544.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, Nat.add_sub_cancel]
  unfold OMA.S_oeis_a008544.a
  simp only [Finset.prod_range_succ]
  push_cast
  ring

