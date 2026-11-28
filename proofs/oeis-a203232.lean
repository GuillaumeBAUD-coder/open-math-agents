import OMAStatements.S_oeis_a203232
import Mathlib

open OMA.S_oeis_a203232 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a203232.main := by
  have r (k : ℕ) : a (k+4) = 12 * a (k+2) - 36 * a k := by
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;>
    simp [a, products, digit, show ∀ c, (2*i+c)%2 = c%2 by omega] <;> ring
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact r (k+1)
  · ext n
    rcases n with _ | _ | _ | _ | n <;> first
    | (simp [-eq_intCast, pow_succ, sub_mul, mul_assoc, r, coeff_X, coeff_one]; ring; done)
    | simp [-eq_intCast, pow_succ, sub_mul, mul_assoc, a, products, digit, coeff_X, coeff_one]
