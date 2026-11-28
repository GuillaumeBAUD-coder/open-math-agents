import OMAStatements.S_oeis_a050446
import Mathlib

/-!
# The counts disagree for a single edge

With one edge and target sum one, the edge may have label zero or
one. In either case both loop labels are determined, so there are
two labelings. A one-letter word on a one-letter alphabet has just
one choice.
-/

open OMA.S_oeis_a050446 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a050446.main) := by
  intro h
  have htable : tableValue 1 1 = 2 := by decide
  have hword : wordCount 1 1 = 1 := by decide
  have hcount := h 1 1
  rw [htable, hword] at hcount
  omega
