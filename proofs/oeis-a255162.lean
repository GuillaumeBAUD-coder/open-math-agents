import OMAStatements.S_oeis_a255162
import Mathlib

open OMA.S_oeis_a255162 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a255162.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [a, AB]
    ring
  · rw [show (12:ℚ⟦X⟧) = C 12 from (map_ofNat _ _).symm,
      show (2:ℚ⟦X⟧) = C 2 from (map_ofNat _ _).symm]
    ext n
    rcases n with _ | _ | n <;> simp [mul_sub, mul_add, ← mul_assoc, pow_succ, a, AB] <;> ring
