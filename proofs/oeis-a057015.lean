import OMAStatements.S_oeis_a057015

/-! Every excluded residue yields a small proper divisor of one of the four primes. -/

theorem OMA.solution : type_of% @OMA.S_oeis_a057015.main := by
  intro k ⟨h1, _, _, h9⟩ hk
  have hsq := Nat.pow_mod k 2 10
  have hk4 : 9 ≤ k ^ 2 := by nlinarith
  have hr : k % 10 < 10 := Nat.mod_lt _ (by decide)
  by_contra hne
  have bad : 2 ∣ k ^ 2 + 1 ∨ 5 ∣ k ^ 2 + 1 ∨ 5 ∣ k ^ 2 + 9 := by
    interval_cases h : k % 10 <;> omega
  rcases bad with h | h | h
  all_goals
    first | have := h1.eq_one_or_self_of_dvd _ h | have := h9.eq_one_or_self_of_dvd _ h
    omega
