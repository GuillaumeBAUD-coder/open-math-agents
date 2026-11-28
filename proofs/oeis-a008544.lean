import OMAStatements.S_oeis_a008544

-- Problem: A008544, the four-term Mathar recurrence for Product_{k<n} (3k+2).
-- Credit: @ShoQo
-- Proof: write n = m + 3 and peel the last three factors off the product.

open OMA.S_oeis_a008544 in
theorem OMA.solution : type_of% @OMA.S_oeis_a008544.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [a, show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, Finset.prod_range_succ]
  push_cast
  ring
