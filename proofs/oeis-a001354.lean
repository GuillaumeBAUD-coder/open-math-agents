import OMAStatements.S_oeis_a001354

open OMA.S_oeis_a001354 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001354.main := by
  have f : ∀ m, Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := fun m => Nat.fib_add_two
  have key : ∀ k, coordination (k + 1) = 7 * Nat.fib (2 * k + 2) ∧
      coordination (k + 2) = 7 * Nat.fib (2 * k + 4) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have e : coordination (k + 3) = 3 * coordination (k + 2) - coordination (k + 1) := rfl
      have h3 := f (2 * k + 2)
      have h4 := f (2 * k + 3)
      have h5 := f (2 * k + 4)
      ring_nf at *
      omega
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h1, h2⟩ := key j
  have h3 := f (2 * j + 2)
  ring_nf at *
  omega
