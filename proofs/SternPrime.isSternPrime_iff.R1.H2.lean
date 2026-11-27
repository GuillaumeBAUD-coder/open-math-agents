import OMAReductions.R_SternPrime_isSternPrime_iff_R1

/-!
Credit: Hanan Beer (@hananzlt), for discharging this reduction step.
The finite verification is the existing Formal Conjectures theorem
SternPrime.isSternPrime_known_examples. Reduction by @ihateSAS.
The claim that there are no further Stern primes remains open.
-/

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  apply SternPrime.isSternPrime_known_examples q
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
    List.mem_cons, List.not_mem_nil, or_false] using hq
