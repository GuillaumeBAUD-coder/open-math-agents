import OMAStatements.S_oeis_a195673
import Mathlib

namespace A195673Proof

open OMA.S_oeis_a195673 Polynomial

theorem T_zero (p q : ℤ) : ∀ n k : ℕ, n < k → T p q n k = 0
  | 0, k, h => by
    have : k ≠ 0 := by omega
    simp [T, this]
  | 1, k, h => by
    have : k ≠ 0 := by omega
    simp [T, this]
  | n + 2, k, h => by
    have h2 : 2 ≤ k := by omega
    simp [T, h2, T_zero p q (n + 1) k (by omega), T_zero p q n (k - 2) (by omega)]

theorem poly_rec (p q : ℤ) (n : ℕ) :
    poly p q (n + 2) = X * poly p q (n + 1) - poly p q n := by
  have e1 : ∑ k ∈ Finset.range (n + 2 + 1), C (T p q (n + 1) k) * X ^ (n + 2 - k)
      = X * poly p q (n + 1) := by
    rw [Finset.sum_range_succ, T_zero p q (n + 1) (n + 2) (by omega)]
    simp only [map_zero, zero_mul, add_zero, poly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n + 1 := by
      have := Finset.mem_range.mp hk
      omega
    have : n + 2 - k = (n + 1 - k) + 1 := by omega
    rw [this, pow_succ]
    ring
  have e2 : ∑ k ∈ Finset.range (n + 2 + 1),
      C (if 2 ≤ k then T p q n (k - 2) else 0) * X ^ (n + 2 - k) = poly p q n := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [poly]
  rw [← e1, ← e2, ← Finset.sum_sub_distrib]
  unfold poly
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [T, C_sub, sub_mul]

theorem poly_diff (p q : ℤ) : ∀ n : ℕ,
    poly (p + 1) (q + 1) n - poly p q n = Chebyshev.S ℤ (n : ℤ)
  | 0 => by simp [poly, T]
  | 1 => by
    simp [poly, T, Finset.sum_range_succ]
    ring
  | n + 2 => by
    have h := Chebyshev.S_add_two ℤ (n : ℤ)
    rw [poly_rec, poly_rec]
    push_cast
    have h1 := poly_diff p q (n + 1)
    push_cast at h1
    rw [h, ← poly_diff p q n, ← h1]
    ring

end A195673Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a195673.main := A195673Proof.poly_diff
