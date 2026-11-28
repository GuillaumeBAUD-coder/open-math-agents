import OMAStatements.S_oeis_a121754
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a121754

/-- The inhomogeneous factor of the defining recurrence of A121754, at index `k + 3`. -/
noncomputable def decoEvenG (k : ℕ) : ℚ :=
  (k : ℚ) + 3 - 2 + (1 / 2) * (1 + (-1 : ℚ) ^ (k + 2)) * ((k : ℚ) + 3 - 1)

/-- The factor in the first-order relation `a (k + 3) = (k + 3) a (k + 2) + k! Q k`. -/
noncomputable def decoEvenQ (k : ℕ) : ℚ :=
  if k % 2 = 0 then ((k : ℚ) + 2) ^ 2 * (2 * (k : ℚ) + 3) / 4
  else ((k : ℚ) + 1) ^ 2 * (2 * (k : ℚ) + 5) / 4

theorem decoEven_step (k : ℕ) : a (k + 3) = (2 * (k : ℚ) + 3) * a (k + 2) -
    ((k : ℚ) + 2) * (k : ℚ) * a (k + 1) + ((k + 1).factorial : ℚ) * decoEvenG k := by
  rw [a, decoEvenG]
  ring

theorem decoEvenQ_even (k : ℕ) (h : k % 2 = 0) :
    decoEvenQ k = ((k : ℚ) + 2) ^ 2 * (2 * (k : ℚ) + 3) / 4 := by
  rw [decoEvenQ, if_pos h]

theorem decoEvenQ_odd (k : ℕ) (h : k % 2 = 1) :
    decoEvenQ k = ((k : ℚ) + 1) ^ 2 * (2 * (k : ℚ) + 5) / 4 := by
  rw [decoEvenQ, if_neg (by omega)]

theorem decoEvenQ_succ (k : ℕ) :
    decoEvenQ (k + 1) = decoEvenQ k + ((k : ℚ) + 2) * decoEvenG (k + 1) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [decoEvenQ_even (2 * j) (by omega), decoEvenQ_odd (2 * j + 1) (by omega), decoEvenG,
      Odd.neg_one_pow ⟨j + 1, by ring⟩]
    push_cast
    ring
  · rw [decoEvenQ_odd (2 * j + 1) (by omega), decoEvenQ_even (2 * j + 1 + 1) (by omega), decoEvenG,
      Even.neg_one_pow ⟨j + 2, by ring⟩]
    push_cast
    ring

theorem decoEven_first (k : ℕ) :
    a (k + 3) = ((k : ℚ) + 3) * a (k + 2) + (k.factorial : ℚ) * decoEvenQ k := by
  induction k with
  | zero =>
    rw [decoEven_step, decoEvenQ_even 0 rfl, decoEvenG]
    norm_num [a]
  | succ k ih =>
    have e := decoEven_step (k + 1)
    simp only [Nat.add_assoc, Nat.reduceAdd] at e ih ⊢
    rw [e, decoEvenQ_succ, Nat.factorial_succ, Nat.factorial_succ k]
    have ih' : ((k : ℚ) + 3) * a (k + 2) = a (k + 3) - (k.factorial : ℚ) * decoEvenQ k := by
      rw [ih]; ring
    push_cast
    linear_combination (-((k : ℚ) + 1)) * ih'

theorem decoEven_fac (m : ℕ) :
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
theorem OMA.solution : type_of% @OMA.S_oeis_a121754.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega]
  rcases m with _ | m
  · have p6 := decoEven_first 3
    have p5 := decoEven_first 2
    have p4 := decoEven_first 1
    have p3 := decoEven_first 0
    rw [decoEvenQ_odd 3 rfl] at p6
    rw [decoEvenQ_even 2 rfl] at p5
    rw [decoEvenQ_odd 1 rfl] at p4
    rw [decoEvenQ_even 0 rfl] at p3
    norm_num at p6 p5 p4 p3 ⊢
    rw [p6, p5, p4, p3]
    ring
  · have p7 := decoEven_first (m + 4)
    have p6 := decoEven_first (m + 3)
    have p5 := decoEven_first (m + 2)
    have p4 := decoEven_first (m + 1)
    have p3 := decoEven_first m
    simp only [Nat.add_assoc, Nat.reduceAdd] at p7 p6 p5 p4 p3 ⊢
    obtain ⟨f1, f2, f3, f4⟩ := decoEven_fac m
    rw [p7, p6, p5, p4, p3, f1, f2, f3, f4]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [decoEvenQ_even m h, decoEvenQ_odd (m + 1) (by omega), decoEvenQ_even (m + 2) (by omega),
        decoEvenQ_odd (m + 3) (by omega), decoEvenQ_even (m + 4) (by omega)]
      push_cast
      ring
    · rw [decoEvenQ_odd m h, decoEvenQ_even (m + 1) (by omega), decoEvenQ_odd (m + 2) (by omega),
        decoEvenQ_even (m + 3) (by omega), decoEvenQ_odd (m + 4) (by omega)]
      push_cast
      ring
