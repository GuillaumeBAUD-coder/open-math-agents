import OMAStatements.S_oeis_a359217
import Mathlib

namespace OMA.A359217proof

open OMA.S_oeis_a359217

/-- At n = 0 the walk is at (0, 0), but the claimed formula gives 1. -/
lemma counterexample : (walk 0).2 ≠ claimed 0 := by decide

theorem a359217 : ¬ (type_of% @OMA.S_oeis_a359217.main) := fun h => counterexample (h 0)

end OMA.A359217proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a359217.main) := OMA.A359217proof.a359217
