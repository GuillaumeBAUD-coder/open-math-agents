import OMAStatements.S_oeis_a359217
import Mathlib

/-!
# A359217: the closed form for the walk's second coordinate fails at `n = 0`

The walk starts at `(0, 0)`, so its second coordinate at step `0` is `0`.

The claimed formula at `n = 0`: `ringIndex 0 = (√1 - 1)/2 = 0`, so `r = 0`, `t = 0`, `s = 1`,
and `a = 11/16`, `b = 7/16`, `c = 3/16` all round down to `0`. The formula then evaluates to
`1 - a - t/2 = 1`, not `0`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a359217.main) := by
  intro h
  -- the claimed identity at n = 0 reads 0 = 1, which evaluation refutes
  have h0 := h 0
  revert h0
  decide
