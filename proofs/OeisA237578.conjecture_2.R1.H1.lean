import OMAReductions.R_OeisA237578_conjecture_2_R1

/-!
# Step OeisA237578.conjecture_2.R1.H1

Hypothesis H1 of reduction OeisA237578.conjecture_2.R1: the finite direction
`a 5 = a 8 = a 13 = 1`, where `a n` counts the `0 < k < n` with `primeCounting (k * n)` prime.

Credit: @ymkaddur

By hand: `primeCounting (5 k)` for `k = 1..4` is `3, 4, 6, 8`; `primeCounting (8 k)` for
`k = 1..7` is `4, 6, 9, 11, 12, 15, 16`; `primeCounting (13 k)` for `k = 1..12` is
`6, 9, 12, 15, 18, 21, 24, 27, 30, 31, 34, 36`. Exactly one prime in each list (3, 11, 31).
Each case is a closed computation, checked by the kernel with `decide`.
-/

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  unfold OMA.R_OeisA237578_conjecture_2_R1.H1
  rintro n (rfl | rfl | rfl) <;> decide
