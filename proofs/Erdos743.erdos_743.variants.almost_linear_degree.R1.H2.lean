import OMAReductions.R_Erdos743_erdos_743_variants_almost_linear_degree_R1

/-!
Proof of `OMA.R_Erdos743_erdos_743_variants_almost_linear_degree_R1.H2`.

For `n ≥ 16`, every `k` with `n / 8 + 1 ≤ k ≤ 7 n / 8` lies in `[2, n]` and satisfies
`n ≤ 8 k ≤ 7 n`. That interval has `7 n / 8 - n / 8` elements, and
`8 (7 n / 8 - n / 8) ≥ (7 n - 7) - n ≥ 5 n`.
-/

open Filter

theorem OMA.solution : OMA.R_Erdos743_erdos_743_variants_almost_linear_degree_R1.H2 := by
  filter_upwards [eventually_ge_atTop 16] with n hn
  refine le_trans ?_ (Nat.mul_le_mul_left 8
    (Finset.card_le_card (s := Finset.Icc (n / 8 + 1) (7 * n / 8)) ?_))
  · rw [Nat.card_Icc]
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    omega
