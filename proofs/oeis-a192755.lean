import OMAStatements.S_oeis_a192755
import Mathlib

def OMA.u : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | n+1 => ((u n).1 + (u n).2, (u n).1 + 5*n+6)

open Polynomial OMA OMA.S_oeis_a192755 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192755.main := by
  have m : (X^2 - X - 1 : ℤ[X]).Monic := by monicity!
  have A (n : ℕ) : a n = (u n).1 := by
    have ⟨s, hs⟩ : ∃ s, p n = (X^2-X-1)*s + (C (u n).2 + C (u n).1 * X) := by
      induction n with
      | zero => exact ⟨0, by simp [p, u]⟩
      | succ n ih =>
        obtain ⟨s, hs⟩ := ih
        exact ⟨X*s + C (u n).1, by simp [p, u, hs]; ring⟩
    rw [a, hs, add_modByMonic, self_mul_modByMonic m, (modByMonic_eq_self_iff m).2
      ((show degree _ ≤ 1 by compute_degree).trans_lt (by
        rw [show (X^2-X-1 : ℤ[X]).degree = 2 by compute_degree!]
        norm_num))]
    simp [-eq_intCast, coeff_C]
  ext (_ | _ | _ | _ | n) <;>
  simp [pow_succ, mul_sub, sub_mul, add_mul, mul_add, ← mul_assoc, PowerSeries.coeff_succ_mul_X,
    PowerSeries.coeff_X, A, u, ← map_ofNat (PowerSeries.C : ℤ →+* _), PowerSeries.coeff_mul_C,
    -eq_intCast] <;> ring
