import OMAStatements.S_oeis_a023554
import Mathlib

/-!
# A023554: convolution of `3, 4, 5, …` with the Fibonacci numbers

Splitting off the last two terms of the convolution and using `F(j + 2) = F(j) + F(j + 1)` in
the others gives `a(n + 3) = a(n + 2) + a(n + 1) + 2n + 9`.  Since
`A022308(m + 2) = A022308(m + 1) + A022308(m) + 1`, the difference
`d(n) = A022308(n + 4) - a(n + 1)` satisfies `d(n + 2) = d(n + 1) + d(n) - 2n - 8`, and so does
`2(n + 5)`; the two agree for `n = 0` (`13 - 3`) and `n = 1` (`22 - 10`).
-/

namespace OMA.S_oeis_a023554

open Finset

/-- The convolution satisfies an inhomogeneous Fibonacci recurrence. -/
lemma a_rec (n : ℕ) : a (n + 3) = a (n + 2) + a (n + 1) + (2 * (n : ℤ) + 9) := by
  have f2 : Nat.fib 2 = 1 := rfl
  have f3 : Nat.fib 3 = 2 := rfl
  have h3 : a (n + 3) = ∑ k ∈ range (n + 1), ((k : ℤ) + 3) * (Nat.fib (n + 3 - k + 1) : ℤ) +
      ((n : ℤ) + 4) * 2 + ((n : ℤ) + 5) * 1 := by
    have e1 : n + 3 - (n + 1) + 1 = 3 := by omega
    have e2 : n + 3 - (n + 2) + 1 = 2 := by omega
    unfold a
    rw [sum_range_succ, sum_range_succ, e1, e2, f2, f3]
    push_cast
    ring
  have h2 : a (n + 2) = ∑ k ∈ range (n + 1), ((k : ℤ) + 3) * (Nat.fib (n + 2 - k + 1) : ℤ) +
      ((n : ℤ) + 4) * 1 := by
    have e1 : n + 2 - (n + 1) + 1 = 2 := by omega
    unfold a
    rw [sum_range_succ, e1, f2]
    push_cast
    ring
  have h1 : a (n + 1) = ∑ k ∈ range (n + 1), ((k : ℤ) + 3) * (Nat.fib (n + 1 - k + 1) : ℤ) := rfl
  have hterm : ∀ k ∈ range (n + 1), ((k : ℤ) + 3) * (Nat.fib (n + 3 - k + 1) : ℤ) =
      ((k : ℤ) + 3) * (Nat.fib (n + 2 - k + 1) : ℤ) +
        ((k : ℤ) + 3) * (Nat.fib (n + 1 - k + 1) : ℤ) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have e3 : n + 3 - k + 1 = (n + 1 - k + 1) + 2 := by omega
    have e2 : n + 2 - k + 1 = (n + 1 - k + 1) + 1 := by omega
    rw [e3, e2, Nat.fib_add_two]
    push_cast
    ring
  rw [h3, h2, h1, sum_congr rfl hterm, sum_add_distrib]
  ring

/-- The other sequence, shifted. -/
lemma A_rec (m : ℕ) : A022308 (m + 2) = A022308 (m + 1) + A022308 m + 1 := rfl

/-- The identity in the form used for induction. -/
lemma key (n : ℕ) : A022308 (n + 4) - a (n + 1) = 2 * ((n : ℤ) + 5) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    have hA : A022308 (n + 6) = A022308 (n + 5) + A022308 (n + 4) + 1 := A_rec (n + 4)
    have ha := a_rec n
    have ih2' : A022308 (n + 5) - a (n + 2) = 2 * (((n : ℤ) + 1) + 5) := by
      have := ih2
      push_cast at this
      exact this
    show A022308 (n + 6) - a (n + 3) = 2 * (((n + 2 : ℕ) : ℤ) + 5)
    push_cast
    linarith

end OMA.S_oeis_a023554

open OMA.S_oeis_a023554 in
theorem OMA.solution : type_of% @OMA.S_oeis_a023554.main := by
  intro n
  exact (key n).symm
