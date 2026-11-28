import OMAStatements.S_oeis_a187044

open OMA.S_oeis_a187044

namespace OMA.P_oeis_a187044

lemma entry_eq_zero (n k : ℕ) (h : n < k) : entry n k = 0 := by
  match n, h with
  | 0, h => rw [entry, if_neg (by omega)]
  | 1, h => rw [entry, if_neg (by omega)]
  | m + 2, h => rw [entry, if_neg (by omega), if_neg (by omega)]

lemma rowSum_rec (n : ℕ) :
    rowSum (n + 2) = rowSum (n + 1) + ((n : ℤ) + 1) * rowSum n + 1 := by
  unfold rowSum
  rw [Finset.sum_range_succ (fun k => entry (n + 2) k) (n + 2)]
  have hlast : entry (n + 2) (n + 2) = 1 := by
    rw [entry, if_neg (by omega), if_pos rfl]
  rw [hlast]
  have hbody : ∀ k ∈ Finset.range (n + 2),
      entry (n + 2) k = entry (n + 1) k + ((n + 1 : ℕ) : ℤ) * entry n k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [entry, if_pos (by omega)]
  rw [Finset.sum_congr rfl hbody, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [show n + 2 = n + 1 + 1 by omega]
  rw [Finset.sum_range_succ (fun k => entry n k) (n + 1), entry_eq_zero n (n + 1) (by omega)]
  push_cast
  ring

end OMA.P_oeis_a187044

open OMA.P_oeis_a187044 in
theorem OMA.solution : type_of% @OMA.S_oeis_a187044.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 := rowSum_rec (m + 1)
  have h2 := rowSum_rec m
  rw [show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at h1
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast at h1 ⊢
  linear_combination h1 - h2
