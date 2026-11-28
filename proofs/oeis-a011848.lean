import OMAStatements.S_oeis_a011848
import Mathlib

/-!
# A011848: the proposed maximum-index description fails at `n = 2`

`a 2 = C(2, 2) / 2 = 0`, but every candidate `k` must satisfy `1 ≤ k`, so `a 2` is not even a
member of `candidates 2` and cannot be its greatest element.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a011848.main) := by
  intro h
  -- membership of `a 2 = 0` would require `1 ≤ 0`
  exact absurd h.1.1 (by decide)
