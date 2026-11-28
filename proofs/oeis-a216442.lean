import OMAStatements.S_oeis_a216442

-- For every k, 5 + 5^k has the distinct representations (1,1,k) and (2,0,k).
-- The original solution and construction are credited to @agchua.
theorem OMA.solution : type_of% @OMA.S_oeis_a216442.main := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 5 + 5 ^ k)
  · intro a b h
    exact Nat.pow_right_injective (by norm_num) (Nat.add_left_cancel h)
  · intro k
    exact ⟨1, 1, k, 2, 0, k, by simp, by norm_num, by norm_num⟩
