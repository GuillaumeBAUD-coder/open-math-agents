import OMAStatements.S_oeis_a239367
import Mathlib

open OMA.S_oeis_a239367 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a239367.main := by
  have B (m : ℕ) : 108 * b (m+1) = 27*2^(m+1) + 36*((m:ℤ)+1)^2 + 48*(m+1) + 8 + 19*(-2)^(m+1) := by
    induction m with
    | zero => simp [b]
    | succ m ih =>
      simp [b, pow_succ] at ih ⊢
      linarith
  have h (k : ℕ) : 27 * a (k+1) = -1 + 4^(k+1) - 12*(k+1) + 36*((k:ℤ)+1)^2 := by
    have := B (2*k)
    simp [a, show 2*(k+1)-1 = 2*k+1 by omega, pow_succ, pow_mul] at this ⊢
    linarith
  have r (k : ℕ) : a (k+5) = 7*a (k+4) - 15*a (k+3) + 13*a (k+2) - 4*a (k+1) := by
    have h5 := h (k+4)
    have h4 := h (k+3)
    have h3 := h (k+2)
    have h2 := h (k+1)
    have h1 := h k
    simp [pow_succ, add_assoc] at h1 h2 h3 h4 h5
    linarith
  refine ⟨fun n hn => ?_, fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simpa using h k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have r1 := r (k+1)
    simp [add_assoc] at r1 ⊢
    linarith [r k]
  · simp only [← map_ofNat (C (R := ℤ))]
    ext n
    rcases n with _ | _ | _ | _ | _ | n <;> first
    | (simp [-eq_intCast, pow_succ, mul_sub, sub_mul, mul_add, ← mul_assoc, r, coeff_X, coeff_one]
       ring; done)
    | simp [-eq_intCast, pow_succ, mul_sub, sub_mul, mul_add, ← mul_assoc, a, b, coeff_X, coeff_one]
