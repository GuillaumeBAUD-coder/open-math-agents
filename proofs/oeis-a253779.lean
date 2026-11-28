import OMAStatements.S_oeis_a253779
import Mathlib

open OMA.S_oeis_a253779 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a253779.main := by
  have E (s c : ℕ) : A001651 (2*s+(c+1)) = 3*s+(3*c+2)/2 := by
    unfold A001651
    omega
  refine ⟨?_, ?_, ?_⟩
  · rintro n h ⟨r, rfl⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ r by omega)
    simp [a, show A001651 (t+1+(t+1)) = 3*t+2 by unfold A001651; omega]
    ring
  · rintro n h ⟨r, rfl⟩
    simp [a, show A001651 (2*r+1) = 3*r+1 by unfold A001651; omega]
    ring
  · rw [show ((X - 1) ^ 6 * (X + 1) ^ 5 : ℚ⟦X⟧) =
      X^11-X^10-5*X^9+5*X^8+10*X^7-10*X^6-10*X^5+10*X^4+5*X^3-5*X^2-X+1 by ring]
    ext (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_mul_C,
      ← map_ofNat (C : ℚ →+* _)] <;>
    first
    | (obtain ⟨s, rfl | rfl⟩ := n.even_or_odd' <;> simp [a, add_assoc, E] <;> ring)
    | norm_num [a, A001651]
