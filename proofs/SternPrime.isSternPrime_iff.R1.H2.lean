import OMAReductions.R_SternPrime_isSternPrime_iff_R1
import Mathlib

-- Step SternPrime.isSternPrime_iff.R1.H2: hypothesis H2 of reduction SternPrime.isSternPrime_iff.R1
-- Credit: @ivillar
-- H2 := each of 2, 3, 17, 137, 227, 977, 1187, 1493 is a Stern prime.
-- Proof: the upstream file already verifies the eight examples by kernel computation
-- (SternPrime.isSternPrime_known_examples, stated over a List); this only converts the Set
-- membership of the step into membership of that List.

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  unfold OMA.R_SternPrime_isSternPrime_iff_R1.H2
  intro q hq
  apply SternPrime.isSternPrime_known_examples
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
