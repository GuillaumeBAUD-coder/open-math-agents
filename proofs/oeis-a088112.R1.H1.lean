import OMAReductions.R_oeis_a088112_R1
import Mathlib

/-! Step H1 of the reduction of OEIS A088112: `4^2 = 16`, whose digit reversal
`61` is prime, so the family `{k^e | 2 <= k, rev (k^e) prime}` is nonempty for `e = 2`. -/

theorem OMA.solution : OMA.R_oeis_a088112_R1.H1 :=
  ⟨4, by omega, by decide⟩
