import OMAStatements.S_oeis_a121757

open OMA.S_oeis_a121757 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121757.main := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    simp [a, D]
  | succ n ih =>
    intro k hk
    rcases k with _ | k
    · simp [a, D]
    · rw [D]
      split_ifs with h1 h2
      · omega
      · obtain rfl : k = n := by omega
        simp [a]
      · rw [Nat.add_sub_cancel, ← ih k (by omega), ← ih (k+1) (by omega), a, a, a,
          Nat.choose_succ_succ', Nat.factorial_succ (k+1)]
        ring
