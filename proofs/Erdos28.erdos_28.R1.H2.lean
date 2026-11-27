import OMAReductions.R_Erdos28_erdos_28_R1

-- Step Erdos28.erdos_28.R1.H2: hypothesis H2 of reduction Erdos28.erdos_28.R1
-- Credit: @caa1982

open scoped Classical in
theorem OMA.solution : OMA.R_Erdos28_erdos_28_R1.H2 := by
  intro A a n
  simp only [AdditiveCombinatorics.sumRep_def]
  let E : Finset (ℕ × ℕ) := {(a, n - a), (n - a, a)}
  refine (Finset.card_le_card (t := _ ∪ E) ?_).trans
    ((Finset.card_union_le _ E).trans (Nat.add_le_add_left (Finset.card_le_two) _))
  intro p hp
  simp only [E, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
    Set.mem_insert_iff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
  obtain ⟨hsum, h1, h2⟩ := hp
  rcases h1 with rfl | h1A
  · right; left; ext <;> dsimp <;> omega
  · rcases h2 with rfl | h2A
    · right; right; ext <;> dsimp <;> omega
    · left; exact ⟨hsum, h1A, h2A⟩
