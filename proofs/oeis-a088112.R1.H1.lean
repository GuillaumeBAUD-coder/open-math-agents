import OMAReductions.R_oeis_a088112_R1

/-!
# Step H1 of `oeis-a088112`: one square with prime digit reversal

`rev` reverses the decimal digits, so `rev (4 ^ 2) = rev 16 = 61`, which is prime. The witness
`k = 4` therefore satisfies `2 ≤ k` and `(rev (k ^ 2)).Prime`, which is exactly `H1`.
-/

theorem OMA.solution : OMA.R_oeis_a088112_R1.H1 := by
  refine ⟨4, by decide, ?_⟩
  decide
