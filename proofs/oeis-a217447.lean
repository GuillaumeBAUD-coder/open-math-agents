import OMAStatements.S_oeis_a217447
import Mathlib

/-!
Credit: @ivillar
Proof: write G(k) = 0! + 1! + ... + (k-1)!. Since sum_{i<k} (i+1)! = G(k+1) - 1, for N = q + 3
the definition reads a(N) = 4 G(q+2) + 2 G(q+1) - 2 (q+1) G(q) - 4. For n = p + 8 every term of
the recurrence has this form; expanding G(p+j) = G(p) + p! + ... + (p+j-1)! and every factorial
as a multiple of p! turns the claim into a polynomial identity. The case n = 7 is checked
directly.
-/

namespace OMAA217447Helpers
open OMA.S_oeis_a217447

def G (k : ℕ) : ℤ := ∑ i ∈ Finset.range k, (i.factorial : ℤ)

theorem Gs (k : ℕ) : G (k + 1) = G k + (k.factorial : ℤ) := by
  unfold G
  rw [Finset.sum_range_succ]

theorem Fdef (k : ℕ) : ∑ i ∈ Finset.range k, ((i + 1).factorial : ℤ) = G (k + 1) - 1 := by
  unfold G
  rw [Finset.sum_range_succ']
  simp

theorem aq (N q q1 q2 : ℕ) (hN : N = q + 3) (h1 : q1 = q + 1) (h2 : q2 = q + 2) :
    a N = 4 * G q2 + 2 * G q1 - 2 * ((q : ℤ) + 1) * G q - 4 := by
  subst hN h1 h2
  unfold a
  rw [show q + 3 - 2 = q + 1 by omega, show q + 3 - 3 = q by omega, Fdef (q + 1), Fdef q,
    show ∑ i ∈ Finset.range q, (i.factorial : ℤ) = G q from rfl]
  push_cast
  ring

end OMAA217447Helpers

open OMAA217447Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a217447.main := by
  intro n hn
  rcases Nat.lt_or_ge n 8 with h8 | h8
  · obtain rfl : n = 7 := by omega
    decide
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 8 := ⟨n - 8, by omega⟩
    rw [show p + 8 - 1 = p + 7 by omega, show p + 8 - 2 = p + 6 by omega,
      show p + 8 - 3 = p + 5 by omega, show p + 8 - 4 = p + 4 by omega,
      show p + 8 - 5 = p + 3 by omega,
      aq (p + 8) (p + 5) (p + 6) (p + 7) (by omega) (by omega) (by omega),
      aq (p + 7) (p + 4) (p + 5) (p + 6) (by omega) (by omega) (by omega),
      aq (p + 6) (p + 3) (p + 4) (p + 5) (by omega) (by omega) (by omega),
      aq (p + 5) (p + 2) (p + 3) (p + 4) (by omega) (by omega) (by omega),
      aq (p + 4) (p + 1) (p + 2) (p + 3) (by omega) (by omega) (by omega),
      aq (p + 3) p (p + 1) (p + 2) (by omega) (by omega) (by omega)]
    have g7 : G (p + 7) = G (p + 6) + ((p + 6).factorial : ℤ) := Gs (p + 6)
    have g6 : G (p + 6) = G (p + 5) + ((p + 5).factorial : ℤ) := Gs (p + 5)
    have g5 : G (p + 5) = G (p + 4) + ((p + 4).factorial : ℤ) := Gs (p + 4)
    have g4 : G (p + 4) = G (p + 3) + ((p + 3).factorial : ℤ) := Gs (p + 3)
    have g3 : G (p + 3) = G (p + 2) + ((p + 2).factorial : ℤ) := Gs (p + 2)
    have g2 : G (p + 2) = G (p + 1) + ((p + 1).factorial : ℤ) := Gs (p + 1)
    have g1 : G (p + 1) = G p + (p.factorial : ℤ) := Gs p
    have f6 : (p + 6).factorial = (p + 6) * (p + 5).factorial := Nat.factorial_succ (p + 5)
    have f5 : (p + 5).factorial = (p + 5) * (p + 4).factorial := Nat.factorial_succ (p + 4)
    have f4 : (p + 4).factorial = (p + 4) * (p + 3).factorial := Nat.factorial_succ (p + 3)
    have f3 : (p + 3).factorial = (p + 3) * (p + 2).factorial := Nat.factorial_succ (p + 2)
    have f2 : (p + 2).factorial = (p + 2) * (p + 1).factorial := Nat.factorial_succ (p + 1)
    have f1 : (p + 1).factorial = (p + 1) * p.factorial := Nat.factorial_succ p
    rw [g7, g6, g5, g4, g3, g2, g1, f6, f5, f4, f3, f2, f1]
    push_cast
    ring
