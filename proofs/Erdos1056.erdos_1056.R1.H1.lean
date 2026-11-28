import OMAReductions.R_Erdos1056_erdos_1056_R1

/-!
# Proof of `Erdos1056.erdos_1056.R1.H1`

Proves the `k = 2` case of Erdős Problem 1056 using Erdős's witness `p = 11` with boundaries
`![3, 5, 8]` (so `3 * 4 ≡ 5 * 6 * 7 ≡ 1 [MOD 11]`).
-/

theorem OMA.solution : OMA.R_Erdos1056_erdos_1056_R1.H1 := by
  refine ⟨11, by decide, ![3, 5, 8], ?_, Erdos1056.erdos_1056.variants.k2⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
