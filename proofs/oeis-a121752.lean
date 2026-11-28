import OMAStatements.S_oeis_a121752
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a121752

/-- The inhomogeneous factor of the defining recurrence of A121752, at index `k + 3`. -/
noncomputable def decoOddG (k : ℕ) : ℚ :=
  ((k : ℚ) + 3) * (((k + 3) / 2 : ℕ) : ℚ) - ((k : ℚ) + 1) * (((k + 2) / 2 : ℕ) : ℚ) - 1

/-- The factor in the first-order relation `a (k + 3) = (k + 3) a (k + 2) + k! Q k`. -/
noncomputable def decoOddQ (k : ℕ) : ℚ :=
  if k % 2 = 0 then ((k : ℚ) + 2) ^ 2 * (2 * (k : ℚ) + 1) / 4
  else ((k : ℚ) + 1) * (2 * (k : ℚ) ^ 2 + 9 * (k : ℚ) + 11) / 4

theorem decoOdd_step (k : ℕ) : a (k + 3) = (2 * (k : ℚ) + 3) * a (k + 2) -
    ((k : ℚ) + 2) * (k : ℚ) * a (k + 1) + ((k + 1).factorial : ℚ) * decoOddG k := by
  rw [a, decoOddG]
  ring

theorem decoOddQ_even (k : ℕ) (h : k % 2 = 0) :
    decoOddQ k = ((k : ℚ) + 2) ^ 2 * (2 * (k : ℚ) + 1) / 4 := by
  rw [decoOddQ, if_pos h]

theorem decoOddQ_odd (k : ℕ) (h : k % 2 = 1) :
    decoOddQ k = ((k : ℚ) + 1) * (2 * (k : ℚ) ^ 2 + 9 * (k : ℚ) + 11) / 4 := by
  rw [decoOddQ, if_neg (by omega)]

theorem decoOddQ_succ (k : ℕ) :
    decoOddQ (k + 1) = decoOddQ k + ((k : ℚ) + 2) * decoOddG (k + 1) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [decoOddQ_even (2 * j) (by omega), decoOddQ_odd (2 * j + 1) (by omega), decoOddG,
      show (2 * j + 1 + 3) / 2 = j + 2 by omega, show (2 * j + 1 + 2) / 2 = j + 1 by omega]
    push_cast
    ring
  · rw [decoOddQ_odd (2 * j + 1) (by omega), decoOddQ_even (2 * j + 1 + 1) (by omega), decoOddG,
      show (2 * j + 1 + 1 + 3) / 2 = j + 2 by omega, show (2 * j + 1 + 1 + 2) / 2 = j + 2 by omega]
    push_cast
    ring

theorem decoOdd_first (k : ℕ) :
    a (k + 3) = ((k : ℚ) + 3) * a (k + 2) + (k.factorial : ℚ) * decoOddQ k := by
  induction k with
  | zero =>
    rw [decoOdd_step, decoOddQ_even 0 rfl, decoOddG]
    norm_num [a]
  | succ k ih =>
    have e := decoOdd_step (k + 1)
    simp only [Nat.add_assoc, Nat.reduceAdd] at e ih ⊢
    rw [e, decoOddQ_succ, Nat.factorial_succ, Nat.factorial_succ k]
    have ih' : ((k : ℚ) + 3) * a (k + 2) = a (k + 3) - (k.factorial : ℚ) * decoOddQ k := by
      rw [ih]; ring
    push_cast
    linear_combination (-((k : ℚ) + 1)) * ih'

theorem decoOdd_fac (m : ℕ) :
    ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) ∧
    ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) ∧
    ((m + 3).factorial : ℚ) = ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) ∧
    ((m + 4).factorial : ℚ) =
      ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.factorial_succ]; push_cast; ring
  · rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  · rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  · rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a121752.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega]
  rcases m with _ | m
  · have p6 := decoOdd_first 3
    have p5 := decoOdd_first 2
    have p4 := decoOdd_first 1
    have p3 := decoOdd_first 0
    rw [decoOddQ_odd 3 rfl] at p6
    rw [decoOddQ_even 2 rfl] at p5
    rw [decoOddQ_odd 1 rfl] at p4
    rw [decoOddQ_even 0 rfl] at p3
    norm_num at p6 p5 p4 p3 ⊢
    rw [p6, p5, p4, p3]
    ring
  · have p7 := decoOdd_first (m + 4)
    have p6 := decoOdd_first (m + 3)
    have p5 := decoOdd_first (m + 2)
    have p4 := decoOdd_first (m + 1)
    have p3 := decoOdd_first m
    simp only [Nat.add_assoc, Nat.reduceAdd] at p7 p6 p5 p4 p3 ⊢
    obtain ⟨f1, f2, f3, f4⟩ := decoOdd_fac m
    rw [p7, p6, p5, p4, p3, f1, f2, f3, f4]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [decoOddQ_even m h, decoOddQ_odd (m + 1) (by omega), decoOddQ_even (m + 2) (by omega),
        decoOddQ_odd (m + 3) (by omega), decoOddQ_even (m + 4) (by omega)]
      push_cast
      ring
    · rw [decoOddQ_odd m h, decoOddQ_even (m + 1) (by omega), decoOddQ_odd (m + 2) (by omega),
        decoOddQ_even (m + 3) (by omega), decoOddQ_odd (m + 4) (by omega)]
      push_cast
      ring
