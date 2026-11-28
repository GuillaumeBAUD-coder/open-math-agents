import OMAStatements.S_oeis_a054109
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: a(n)+a(n-1)=b(n) reduces the recurrence to (n+2)C(2n+3,n+2)=2(2n+3)C(2n+1,n+1) (Pascal-type choose identities). No computer search.

namespace OMA.A054109Proof

open OMA.S_oeis_a054109
theorem a_succ (n : ℕ) : a (n + 1) = (b (n + 1) : ℤ) - a n := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
  have : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + 1 - k) * (b k : ℤ)
      = -∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (b k : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring
  rw [this]; ring

theorem b_rec (n : ℕ) : (n + 2) * b (n + 1) = 2 * (2 * n + 3) * b n := by
  unfold b
  have e1 := Nat.add_one_mul_choose_eq (2 * n + 2) (n + 1)
  have e2 := Nat.add_one_mul_choose_eq (2 * n + 1) n
  have e3 : (2 * n + 1).choose n = (2 * n + 1).choose (n + 1) := (Nat.choose_symm_half n).symm
  rw [show 2 * (n + 1) + 1 = 2 * n + 2 + 1 by ring, show n + 1 + 1 = n + 1 + 1 from rfl]
  rw [e3] at e2
  have e4 : (2 * n + 2).choose (n + 1) = 2 * (2 * n + 1).choose (n + 1) := by
    have : (n + 1) * (2 * (2 * n + 1).choose (n + 1)) = (n + 1) * (2 * n + 2).choose (n + 1) := by
      rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at e2; nlinarith [e2]
    exact (Nat.eq_of_mul_eq_mul_left (by omega) this).symm
  rw [show 2 * n + 2 + 1 = 2 * n + 3 by ring] at e1 ⊢
  rw [show 2 * n + 2 + 1 = 2 * n + 3 by ring] at e1
  nlinarith [e1, e4]

theorem mainP : ∀ n : ℕ, 2 ≤ n → ((n : ℤ) + 1) * a n + (-3 * (n : ℤ) - 1) * a (n - 1) + 2 * (-2 * (n : ℤ) - 1) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  rw [a_succ (m + 1), a_succ m]
  have h := b_rec (m + 1)
  have h' : ((m : ℤ) + 1 + 2) * (b (m + 1 + 1) : ℤ) = 2 * (2 * ((m : ℤ) + 1) + 3) * b (m + 1) := by exact_mod_cast h
  push_cast
  linear_combination h'

end OMA.A054109Proof

open OMA.A054109Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a054109.main := mainP
