import OMAStatements.S_oeis_a005560
import Mathlib

open OMA.S_oeis_a005560 in
theorem OMA.solution : type_of% @OMA.S_oeis_a005560.main := by
  have F (t : ℕ) : a (t+3) = ((t+4).choose ((t+2)/2) : ℚ) * (t+3).choose ((t+1)/2) -
      ((t+4).choose ((t+1)/2) : ℚ) * (t+3).choose (t/2) := by
    rw [a, column]
    simp only [show 2+t+1 = t+3 by omega, show t+3+1 = t+4 from rfl]
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rcases k with _ | k
  · norm_num [a, column, Nat.choose]
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;>
  simp (disch := omega) [F, add_assoc, show ∀ c, (2*i+c)/2 = i+c/2 by omega, Nat.cast_choose ℚ,
    show ∀ m c, m ≤ c → 2*i+c-(i+m) = i+(c-m) by omega, show ∀ c, 2*i+c-i = i+c by omega,
    Nat.factorial_succ] <;>
  field_simp <;> ring
