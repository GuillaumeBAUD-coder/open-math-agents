import OMAStatements.S_oeis_a377118

open OMA.S_oeis_a377118 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377118.main) := fun h => by
  obtain ⟨_, p⟩ := ((h 2 Nat.prime_two).2 [1] (by simp [displayed])).1
  have e : Nat.count (fun n => 2 ∣ a n) 2 = 1 := by decide
  have := p 0
  rw [gap, zero_add, Nat.nth_zero_of_zero (by decide), ← e, Nat.nth_count (by decide)] at this
  simp [e, Nat.mod_one] at this
