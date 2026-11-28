import OMAStatements.S_oeis_a050446

/-!
# The counts disagree for a single edge

With one edge and target sum one, the edge may have label zero or
one. In either case both loop labels are determined, so there are
two labelings. A one-letter word on a one-letter alphabet has just
one choice.
-/

open OMA.S_oeis_a050446 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a050446.main) := by
  exact fun h => (by decide : tableValue 1 1 ≠ wordCount 1 1) (h 1 1)
