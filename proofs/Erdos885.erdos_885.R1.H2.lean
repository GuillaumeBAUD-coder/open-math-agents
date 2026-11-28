import OMAReductions.R_Erdos885_erdos_885_R1

/-!
Proof of `OMA.R_Erdos885_erdos_885_R1.H2`.
For `k = 2, 3, 4` explicit families of `k` numbers whose factor-difference sets share at least
`k` elements are the witnesses `erdos_885.variants.k_eq_2`, `k_eq_3` and `k_eq_4` proved in the
formal-conjectures file for Erdős problem 885; split into these three cases.
-/

theorem OMA.solution : OMA.R_Erdos885_erdos_885_R1.H2 := by
  intro k hk2 hk4
  interval_cases k
  · exact Erdos885.erdos_885.variants.k_eq_2
  · exact Erdos885.erdos_885.variants.k_eq_3
  · exact Erdos885.erdos_885.variants.k_eq_4
