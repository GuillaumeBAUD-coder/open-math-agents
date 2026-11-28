import OMAStatements.S_oeis_a192249
import Mathlib

def OMA.u : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 1, 0)
  | n+1 => ((u n).2.1, (u n).1 + (u n).2.1, (u n).2.2.1 + (n+5).choose 4 * (u n).2.1,
      (u n).2.2.2 + (n+5).choose 4 * ((u n).1 + (u n).2.1))

set_option maxHeartbeats 4000000 in
open Polynomial OMA OMA.S_oeis_a192249 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192249.main := by
  have m : (X^2 - X - 1 : ℤ[X]).Monic := by monicity!
  have A (n : ℕ) : a (n+1) = (u n).2.2.2 := by
    have ⟨t, s, ht, hs⟩ : ∃ t s, (X:ℤ[X])^n = (X^2-X-1)*t + (C (u n).1 + C (u n).2.1 * X) ∧
        p n = (X^2-X-1)*s + (C (u n).2.2.1 + C (u n).2.2.2 * X) := by
      induction n with
      | zero => exact ⟨0, 0, by simp [u], by simp [p, u]⟩
      | succ n ih =>
        obtain ⟨t, s, ht, hs⟩ := ih
        have ht' : (X:ℤ[X])^(n+1) = (X^2-X-1)*(X*t + C (u n).2.1) +
            (C (u n).2.1 + C ((u n).1 + (u n).2.1) * X) := by
          rw [pow_succ, ht]
          simp
          ring
        refine ⟨_, s + C (((n+5).choose 4 : ℕ) : ℤ) * (X*t + C (u n).2.1), ht', ?_⟩
        rw [show p (n+1) = p n + C (((n+5).choose 4 : ℕ) : ℤ) * X^(n+1) from
          Finset.sum_range_succ _ _, hs, ht']
        simp [u]
        ring
    rw [a, Nat.add_sub_cancel, hs, add_modByMonic, self_mul_modByMonic m,
      (modByMonic_eq_self_iff m).2 ((show degree _ ≤ 1 by compute_degree).trans_lt (by
        rw [show (X^2-X-1 : ℤ[X]).degree = 2 by compute_degree!]
        norm_num))]
    simp [-eq_intCast, coeff_C]
  have q (n : ℕ) : (((n+4).choose 4 : ℕ) : ℚ) = (n+1)*(n+2)*(n+3)*(n+4)/24 := by
    rw [Nat.cast_choose ℚ (show 4 ≤ n+4 by omega), Nat.add_sub_cancel]
    simp [Nat.factorial_succ]
    field_simp
    ring
  rw [mul_comm PowerSeries.X, mul_assoc, show (PowerSeries.X * ((PowerSeries.X - 1) *
    (PowerSeries.X^2+PowerSeries.X-1)^5) : PowerSeries ℚ) = PowerSeries.X^12+4*PowerSeries.X^11
    -15*PowerSeries.X^9-5*PowerSeries.X^8+26*PowerSeries.X^7+4*PowerSeries.X^6-25*PowerSeries.X^5
    +5*PowerSeries.X^4+10*PowerSeries.X^3-6*PowerSeries.X^2+PowerSeries.X by ring]
  ext (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n) <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_X,
    PowerSeries.coeff_mul_C, ← map_ofNat (PowerSeries.C : ℚ →+* _), A, u, q] <;> ring
