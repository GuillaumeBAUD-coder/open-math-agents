import OMAStatements.S_oeis_a081923

namespace OMA.S_oeis_a081923

open Finset

def b (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * 2 ^ (n - k) * (k + 2).factorial

lemma two_a (n : ℕ) : 2 * a n =
    ∑ k ∈ range (n + 1), n.choose (k + 1) * 2 ^ (n - k) * (k + 2).factorial + 2 ^ (n + 1) := by
  unfold a
  rw [sum_range_succ', sum_range_succ (fun k => n.choose (k + 1) * 2 ^ (n - k) * (k + 2).factorial),
    Nat.choose_succ_self, mul_add, mul_sum]
  simp only [zero_mul, add_zero, Nat.choose_zero_right, Nat.sub_zero, one_mul, zero_add,
    Nat.factorial_one, mul_one]
  congr 1
  · apply sum_congr rfl
    intro k hk
    have : k < n := mem_range.mp hk
    rw [show n - k = (n - (k + 1)) + 1 by omega, pow_succ]
    ring
  · ring

lemma L1 (n : ℕ) : a (n + 1) = 2 * a n + b n := by
  rw [two_a]
  unfold a b
  rw [sum_range_succ']
  simp only [Nat.choose_succ_succ', add_mul, sum_add_distrib, Nat.choose_zero_right, Nat.sub_zero,
    one_mul, zero_add, Nat.factorial_one, mul_one, show ∀ k, n + 1 - (k + 1) = n - k from
      fun k => by omega]
  ring

lemma L2 (n : ℕ) : b (n + 1) = 2 * a (n + 1) + (n + 1) * b n := by
  have h1 : b (n + 1) = ∑ k ∈ range (n + 2), (n + 1).choose k * 2 ^ (n + 1 - k) * (k + 1).factorial * 2
      + ∑ k ∈ range (n + 2), k * ((n + 1).choose k * 2 ^ (n + 1 - k) * (k + 1).factorial) := by
    unfold b
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    rw [show k + 2 = (k + 1) + 1 by ring, Nat.factorial_succ]
    ring
  have h2 : ∑ k ∈ range (n + 2), k * ((n + 1).choose k * 2 ^ (n + 1 - k) * (k + 1).factorial) =
      (n + 1) * b n := by
    rw [sum_range_succ']
    unfold b
    rw [mul_sum]
    simp only [zero_mul, add_zero]
    apply sum_congr rfl
    intro k _
    have hc : (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
      have := Nat.add_one_mul_choose_eq n k
      linarith [mul_comm ((n + 1).choose (k + 1)) (k + 1)]
    rw [show n + 1 - (k + 1) = n - k by omega, show k + 1 + 1 = k + 2 by ring]
    calc (k + 1) * ((n + 1).choose (k + 1) * 2 ^ (n - k) * (k + 2).factorial)
        = ((k + 1) * (n + 1).choose (k + 1)) * 2 ^ (n - k) * (k + 2).factorial := by ring
      _ = (n + 1) * (n.choose k * 2 ^ (n - k) * (k + 2).factorial) := by rw [hc]; ring
  rw [h1, h2, ← sum_mul]
  unfold a
  ring

theorem solution_main : ∀ n : ℕ, 2 ≤ n → a n + 2 * (n - 1) * a (n - 2) = (n + 3) * a (n - 1) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have e1 := L1 (m + 1)
  have e2 := L2 m
  have e3 := L1 m
  zify at e1 e2 e3 ⊢
  linear_combination e1 + e2 - ((m : ℤ) + 1) * e3

end OMA.S_oeis_a081923

theorem OMA.solution : type_of% @OMA.S_oeis_a081923.main := OMA.S_oeis_a081923.solution_main
