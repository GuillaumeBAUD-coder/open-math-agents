import OMAReductions.R_Erdos28_erdos_28_R1

-- Step Erdos28.erdos_28.R1.H2: hypothesis H2 of reduction Erdos28.erdos_28.R1
-- Credit: @luciusacarr
-- H2 := ∀ (A : Set ℕ) (a n : ℕ), sumRep (insert a A) n ≤ sumRep A n + 2

open AdditiveCombinatorics

theorem OMA.solution : OMA.R_Erdos28_erdos_28_R1.H2 := by
  classical
  intro A a n
  rw [sumRep_def, sumRep_def]
  calc _ ≤ ({p ∈ Finset.HasAntidiagonal.antidiagonal n | p.1 ∈ A ∧ p.2 ∈ A} ∪
        {(a, n - a), (n - a, a)}).card := by
        apply Finset.card_le_card
        rintro ⟨x, y⟩ hp
        simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
          Set.mem_insert_iff] at hp
        obtain ⟨hxy, hx, hy⟩ := hp
        simp only [Finset.mem_union, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
          Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rcases hx with hx | hx
        · right; left; omega
        rcases hy with hy | hy
        · right; right; omega
        · left; exact ⟨hxy, hx, hy⟩
    _ ≤ _ := (Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_le_two)
