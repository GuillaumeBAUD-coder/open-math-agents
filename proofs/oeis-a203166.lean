import OMAStatements.S_oeis_a203166
import Mathlib

open OMA.S_oeis_a203166 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a203166.main := by
  have r (k : ℕ) : a (k+10) = 240 * a (k+5) - 14400 * a k := by
    obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 5 ∧ k = 5*i+j := ⟨k/5, k%5, by omega⟩
    interval_cases j <;>
    simp [a, products, digit, add_assoc, show ∀ c, (5*i+c)%5 = c%5 by omega] <;> ring
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact r (k+1)
  · ext n
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> first
    | (simp [-eq_intCast, pow_succ, sub_mul, mul_assoc, r, coeff_X, coeff_one]; ring; done)
    | simp [-eq_intCast, pow_succ, sub_mul, mul_assoc, a, products, digit, coeff_X, coeff_one]
