import OMAReductions.R_SternPrime_isSternPrime_iff_R1

-- Step SternPrime.isSternPrime_iff.R1.H2 of reduction SternPrime.isSternPrime_iff.R1
-- Credit: @ihateSAS
/-!
# The eight Stern primes are Stern

`H2` of the reduction is the finite half of the exhaustion conjecture: each of
`2, 3, 17, 137, 227, 977, 1187, 1493` is prime and admits no decomposition `p + 2 b^2` with
`p` prime and `b ≥ 1`.

This is a finite verification.  The module already carries it out as
`SternPrime.isSternPrime_known_examples`, stated for the corresponding `List`; this step
transfers it to the `Set` membership used in the reduction.
-/

/-- Set membership in the eight-element literal implies `List` membership, which is the form
in which the module states the verified examples. -/
private lemma mem_list_of_mem_set {q : ℕ}
    (hq : q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ)) :
    q ∈ ([2, 3, 17, 137, 227, 977, 1187, 1493] : List ℕ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  exact SternPrime.isSternPrime_known_examples q (mem_list_of_mem_set hq)
