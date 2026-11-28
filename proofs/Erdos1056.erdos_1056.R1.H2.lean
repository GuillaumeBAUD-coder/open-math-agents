import OMAReductions.R_Erdos1056_erdos_1056_R1

/-!
# Proof of `Erdos1056.erdos_1056.R1.H2`

Proves the `k = 3` case of Erdős Problem 1056 using Makowski's witness `p = 17` with boundaries
`![2, 6, 12, 16]`.
-/

theorem OMA.solution : OMA.R_Erdos1056_erdos_1056_R1.H2 := by
  refine ⟨17, by decide, ![2, 6, 12, 16], ?_, Erdos1056.erdos_1056.variants.k3⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
