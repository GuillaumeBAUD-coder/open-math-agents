import OMAStatements.S_oeis_a054109
import Mathlib

/-!
Credit: @ivillar
Proof: from the alternating-sum definition, a(n + 1) + a(n) = b(n + 1) with
b(n) = C(2n + 1, n + 1), and (n + 2) b(n + 1) = 2 (2n + 3) b(n) (two applications of
Pascal's rule and the symmetry C(2n + 1, n) = C(2n + 1, n + 1)). Then
(n + 1) a(n) - (3n + 1) a(n - 1) - 2 (2n + 1) a(n - 2)
  = (n + 1) b(n) - 2 (2n + 1) (a(n - 1) + a(n - 2)) = (n + 1) b(n) - 2 (2n + 1) b(n - 1) = 0.
-/

namespace OMAA054109Helpers
open OMA.S_oeis_a054109

theorem ha (n : ℕ) : a (n + 1) + a n = (b (n + 1) : ℤ) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
  have h : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + 1 - k) * (b k : ℤ) =
      -∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (b k : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring
  rw [h]
  ring

theorem bstep (n : ℕ) :
    ((n : ℤ) + 2) * (b (n + 1) : ℤ) = 2 * (2 * (n : ℤ) + 3) * (b n : ℤ) := by
  have h1 : (2 * n + 2 + 1) * (2 * n + 2).choose (n + 1) =
      (2 * n + 2 + 1).choose (n + 1 + 1) * (n + 1 + 1) :=
    Nat.add_one_mul_choose_eq (2 * n + 2) (n + 1)
  have h2 : (2 * n + 2).choose (n + 1) = (2 * n + 1).choose n + (2 * n + 1).choose (n + 1) :=
    Nat.choose_succ_succ (2 * n + 1) n
  have h3 : (2 * n + 1).choose (n + 1) = (2 * n + 1).choose n := Nat.choose_symm_half n
  have h1' := congrArg (Nat.cast : ℕ → ℤ) h1
  have h2' := congrArg (Nat.cast : ℕ → ℤ) h2
  have h3' := congrArg (Nat.cast : ℕ → ℤ) h3
  push_cast at h1' h2' h3'
  unfold b
  rw [show 2 * (n + 1) + 1 = 2 * n + 2 + 1 by ring]
  linear_combination (-1 : ℤ) * h1' + (2 * (n : ℤ) + 3) * h2' - (2 * (n : ℤ) + 3) * h3'

end OMAA054109Helpers

open OMAA054109Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a054109.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have e2 := ha (m + 1)
  have e1 := ha m
  have bs := bstep (m + 1)
  rw [show m + 1 + 1 = m + 2 from rfl] at e2 bs
  push_cast at bs ⊢
  linear_combination ((m : ℤ) + 3) * e2 - (4 * (m : ℤ) + 10) * e1 + bs
