import OMAStatements.S_oeis_a173527
import Mathlib

open OMA.S_oeis_a173527 in
theorem OMA.solution : type_of% @OMA.S_oeis_a173527.main := by
  have d (N j : ℕ) (hj : j < 7) : a (7*N + (j+1)) = a (N+1) + j := by
    obtain h | h := Nat.eq_zero_or_pos (7*N+j)
    · simp [a, show N = 0 by omega, show j = 0 by omega]
    · simp [a, ← add_assoc, Nat.digits_def' (by norm_num : 1 < 7) h, show (7*N+j)%7 = j by omega,
        show (7*N+j)/7 = N by omega]
      ring
  refine ⟨by simp [a], fun N => ?_⟩
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append, ih, show 7*(N+1) = 7*N+7 by ring]
    simp [List.range_succ, phi, d, add_assoc]
