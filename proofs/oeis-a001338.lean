import OMAStatements.S_oeis_a001338
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A001338 (statement by @ivillar).
-- Idea: for n ≥ 1, a(n) = -1 + b(n) with b(n) = Sum_j j!*binomial(n,j+1). Pascal's rule gives
-- b(n+1) = b(n) + c(n) with c(n) = Sum_j j!*binomial(n,j) (A000522), and (j+1)*binomial(n+1,j+1) =
-- (n+1)*binomial(n,j) gives c(n+1) = (n+1)*c(n) + 1. Eliminating b and c (the constant terms cancel,
-- since the coefficients of the recurrence sum to 0) yields the recurrence for n ≥ 4.

namespace OMAA001338Helpers

open OMA.S_oeis_a001338

/-- c(n) = Sum_{j=0..n} j! * binomial(n,j). -/
def c (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), (j.factorial : ℤ) * (n.choose j : ℤ)

/-- b(n) = Sum_{j=0..n-1} j! * binomial(n,j+1). -/
def b (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, (j.factorial : ℤ) * (n.choose (j + 1) : ℤ)

theorem hb (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ((k - 1).factorial : ℤ) * (n.choose k : ℤ) = b n := by
  have hI : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega]
  unfold b
  apply Finset.sum_congr rfl
  intro j _
  rw [show 1 + j - 1 = j by omega, add_comm 1 j]

theorem b_succ (n : ℕ) : b (n + 1) = b n + c n := by
  unfold b c
  simp only [Nat.choose_succ_succ', Nat.cast_add, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun j => (j.factorial : ℤ) * (n.choose (j + 1) : ℤ)) n,
    Nat.choose_succ_self]
  push_cast
  ring

theorem c_succ (n : ℕ) : c (n + 1) = ((n : ℤ) + 1) * c n + 1 := by
  unfold c
  rw [Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
  simp only [Nat.factorial_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have h : ((n + 1 : ℕ) : ℤ) * (n.choose j : ℤ) = ((n + 1).choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n j
  rw [Nat.factorial_succ]
  push_cast at h ⊢
  linear_combination (-(j.factorial : ℤ)) * h

theorem ha (n : ℕ) : a (n + 1) = -1 + b (n + 1) := by
  unfold a
  rw [if_neg (by omega), hb]

end OMAA001338Helpers

open OMA.S_oeis_a001338 OMAA001338Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a001338.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega]
  have e4 : a (k + 4) = -1 + b (k + 4) := ha (k + 3)
  have e3 : a (k + 3) = -1 + b (k + 3) := ha (k + 2)
  have e2 : a (k + 2) = -1 + b (k + 2) := ha (k + 1)
  have e1 : a (k + 1) = -1 + b (k + 1) := ha k
  have f3 : b (k + 4) = b (k + 3) + c (k + 3) := b_succ (k + 3)
  have f2 : b (k + 3) = b (k + 2) + c (k + 2) := b_succ (k + 2)
  have f1 : b (k + 2) = b (k + 1) + c (k + 1) := b_succ (k + 1)
  have g3 : c (k + 3) = ((k : ℤ) + 3) * c (k + 2) + 1 := by
    have h := c_succ (k + 2); push_cast at h; linear_combination h
  have g2 : c (k + 2) = ((k : ℤ) + 2) * c (k + 1) + 1 := by
    have h := c_succ (k + 1); push_cast at h; linear_combination h
  linear_combination (norm := (push_cast; ring)) e4 + (-((k + 4 : ℕ) : ℤ) - 1) * e3 +
    2 * (((k + 4 : ℕ) : ℤ) - 1) * e2 + (-((k + 4 : ℕ) : ℤ) + 2) * e1 + f3 - ((k : ℤ) + 4) * f2 +
    ((k : ℤ) + 2) * f1 + g3 - g2

