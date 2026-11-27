import OMAReductions.R_SternPrime_isSternPrime_iff_R1

/- Formal Conjectures checks the eight classical Stern primes as a list.
The finite-set formulation here is the one used in @ihateSAS's reduction. -/
theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  apply SternPrime.isSternPrime_known_examples q
  simpa using hq
