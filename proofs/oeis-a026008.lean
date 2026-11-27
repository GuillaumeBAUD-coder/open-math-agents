import OMAStatements.S_oeis_a026008
import Mathlib

namespace A026008
open OMA.S_oeis_a026008 in
lemma a_even (m : ℕ) : a (2 * m) = evenTerm m := by
  unfold a
  have h1 : 2 * m % 2 = 0 := by omega
  have h2 : 2 * m / 2 = m := by omega
  rw [if_pos h1, h2]

open OMA.S_oeis_a026008 in
lemma a_odd (m : ℕ) : a (2 * m + 1) = oddTerm m := by
  unfold a
  have h1 : ¬ ((2 * m + 1) % 2 = 0) := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [if_neg h1, h2]

open OMA.S_oeis_a026008 in
lemma evenTerm_succ (k : ℕ) :
    evenTerm (k + 1)
      = evenTerm k * ((2 * (k : ℚ) + 4) * (2 * k + 3)) / (((k : ℚ) + 2) * (k + 3)) := by
  unfold evenTerm
  have a1 : (2 * (k + 1) + 2).factorial
      = (2 * k + 2 + 1 + 1) * ((2 * k + 2 + 1) * (2 * k + 2).factorial) := by
    have e : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ]
  have a2 : (k + 2).factorial = (k + 2) * (k + 1).factorial := Nat.factorial_succ (k + 1)
  have a3 : (k + 3).factorial = (k + 3) * (k + 2).factorial := Nat.factorial_succ (k + 2)
  rw [a1, a3, a2]
  have h1 : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

open OMA.S_oeis_a026008 in
lemma oddTerm_eq (k : ℕ) :
    oddTerm k = 3 * ((k : ℚ) + 1) * evenTerm k / ((k : ℚ) + 3) := by
  unfold oddTerm evenTerm
  have b1 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
  have b3 : (k + 3).factorial = (k + 2 + 1) * (k + 2).factorial := Nat.factorial_succ (k + 2)
  rw [b1, b3]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((k + 2).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end A026008

theorem OMA.solution : type_of% @OMA.S_oeis_a026008.main := by
  intro t
  rcases Nat.even_or_odd' t with ⟨k, rfl | rfl⟩
  · have e4 : 2 * k + 4 = 2 * (k + 2) := by ring
    have e3 : 2 * k + 3 = 2 * (k + 1) + 1 := by ring
    have e2 : 2 * k + 2 = 2 * (k + 1) := by ring
    rw [e4, e3, e2, A026008.a_even, A026008.a_odd, A026008.a_even, A026008.a_odd,
      A026008.a_even]
    have E2 : OMA.S_oeis_a026008.evenTerm (k + 2) = _ := A026008.evenTerm_succ (k + 1)
    rw [A026008.oddTerm_eq (k + 1), A026008.oddTerm_eq k, E2, A026008.evenTerm_succ k]
    push_cast
    field_simp
    ring
  · have e5 : 2 * k + 1 + 4 = 2 * (k + 2) + 1 := by ring
    have e4 : 2 * k + 1 + 3 = 2 * (k + 2) := by ring
    have e3 : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by ring
    have e2 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
    rw [e5, e4, e3, e2, A026008.a_odd, A026008.a_even, A026008.a_odd, A026008.a_even,
      A026008.a_odd]
    have E2 : OMA.S_oeis_a026008.evenTerm (k + 2) = _ := A026008.evenTerm_succ (k + 1)
    rw [A026008.oddTerm_eq (k + 2), A026008.oddTerm_eq (k + 1), A026008.oddTerm_eq k, E2,
      A026008.evenTerm_succ k]
    push_cast
    field_simp
    ring
