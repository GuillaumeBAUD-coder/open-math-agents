import OMAReductions.R_SternPrime_isSternPrime_iff_R1

-- Step SternPrime.isSternPrime_iff.R1.H2: hypothesis H2 of reduction SternPrime.isSternPrime_iff.R1
-- Credit: @OrangeHeadz
-- H2 := ∀ q : ℕ, q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ) →     SternPrime.IsSternPrime q

/-- The eight listed numbers, as a list: the finite verification, by kernel evaluation of the
decision procedure that the module provides for `SternPrime.IsSternPrime`. -/
theorem OMA.known_examples :
    ∀ q ∈ ([2, 3, 17, 137, 227, 977, 1187, 1493] : List ℕ), SternPrime.IsSternPrime q := by
  decide +kernel

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact OMA.known_examples _ (by simp)
