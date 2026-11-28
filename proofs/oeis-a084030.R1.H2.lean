import OMAReductions.R_oeis_a084030_R1
import Mathlib

/-! # OEIS A084030 - boundary cases n = 1 and n = 2

`witnesses 1 = {1}` and `witnesses 2 = {20}`: both `Finset.filter`
evaluations are small enough for `decide`. -/

theorem OMA.solution : OMA.R_oeis_a084030_R1.H2 :=
  ⟨by decide, by decide⟩
