import OMAStatements.S_oeis_a192748
import Mathlib

def OMA.u : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | n+1 => ((u n).1 + (u n).2, (u n).1 + 3*n+3)

open Polynomial OMA OMA.S_oeis_a192748 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192748.main := by
  have m : (X^2 - X - 1 : ℤ[X]).Monic := by monicity!
  have A (n : ℕ) : a (n+1) = (u n).1 := by
    have ⟨s, hs⟩ : ∃ s, p n = (X^2-X-1)*s + (C (u n).2 + C (u n).1 * X) := by
      induction n with
      | zero => exact ⟨0, by simp [p, u]⟩
      | succ n ih =>
        obtain ⟨s, hs⟩ := ih
        exact ⟨X*s + C (u n).1, by simp [p, u, hs]; ring⟩
    rw [a, Nat.add_sub_cancel, hs, add_modByMonic, self_mul_modByMonic m,
      (modByMonic_eq_self_iff m).2 ((show degree _ ≤ 1 by compute_degree).trans_lt (by
        rw [show (X^2-X-1 : ℤ[X]).degree = 2 by compute_degree!]
        norm_num))]
    simp [-eq_intCast, coeff_C]
  constructor
  · rw [mul_comm PowerSeries.X, mul_assoc, show (PowerSeries.X * ((PowerSeries.X ^ 2 +
      PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2) : PowerSeries ℚ) = PowerSeries.X^5 -
      PowerSeries.X^4 - 2*PowerSeries.X^3 + 3*PowerSeries.X^2 - PowerSeries.X by ring]
    ext (_ | _ | _ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, mul_add, ← mul_assoc, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_X, PowerSeries.coeff_mul_C, ← map_ofNat (PowerSeries.C : ℚ →+* _), A, u]
      <;> ring
  · ext (_ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, sub_mul, ← mul_assoc, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_X, A, u] <;> ring
