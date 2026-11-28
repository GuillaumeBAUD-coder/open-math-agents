import OMAStatements.S_oeis_a081071
import Mathlib

open OMA.S_oeis_a081071 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081071.main := by
  have l (m : ℕ) : lucas m + m.fib = 2 * (m+1).fib := by
    induction m using Nat.twoStepInduction with
    | zero => simp [lucas]
    | one => simp [lucas]
    | more m h1 h2 =>
      simp [lucas, Nat.fib_add_two] at *
      omega
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h1 := l (4*n+2)
    have h2 := l (4*n+6)
    rw [show 2*(n+1) = 2*n+1+1 by ring, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega)]
    simp only [a, Nat.fib_add_two, mul_add, ← mul_assoc, add_assoc, Nat.reduceMul, Nat.reduceAdd, mul_one] at h1 h2 ih ⊢
    omega
