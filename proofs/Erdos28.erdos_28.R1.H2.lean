import OMAReductions.R_Erdos28_erdos_28_R1

-- Step Erdos28.erdos_28.R1.H2: hypothesis H2 of reduction Erdos28.erdos_28.R1
-- Credit: @abdullahcengil
-- H2 := ∀ (A : Set ℕ) (a n : ℕ), sumRep (insert a A) n ≤ sumRep A n + 2

/-!
# Step `H2` of `Erdos28.erdos_28.R1`

Inserting one element `a` into `A` creates at most two new ordered representations of `n`.
An ordered pair `(x, y)` with `x + y = n` and both coordinates in `insert a A` either has both
coordinates in `A`, or has `x = a` (so it is `(a, n - a)`), or has `y = a` (so it is `(n - a, a)`).
-/

open AdditiveCombinatorics

theorem OMA.solution : OMA.R_Erdos28_erdos_28_R1.H2 := by
  unfold OMA.R_Erdos28_erdos_28_R1.H2
  intro A a n
  classical
  simp only [sumRep_def]
  calc _ ≤ ((Finset.HasAntidiagonal.antidiagonal n).filter
            (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A) ∪ {(a, n - a), (n - a, a)}).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
          Set.mem_insert_iff] at hp
        obtain ⟨hsum, h1, h2⟩ := hp
        simp only [Finset.mem_union, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
          Finset.mem_insert, Finset.mem_singleton]
        rcases h1 with h1 | h1
        · exact Or.inr (Or.inl (Prod.ext h1 (show p.2 = n - a by omega)))
        · rcases h2 with h2 | h2
          · exact Or.inr (Or.inr (Prod.ext (show p.1 = n - a by omega) h2))
          · exact Or.inl ⟨hsum, h1, h2⟩
    _ ≤ ((Finset.HasAntidiagonal.antidiagonal n).filter
            (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)).card +
          ({(a, n - a), (n - a, a)} : Finset (ℕ × ℕ)).card := Finset.card_union_le _ _
    _ ≤ _ := by
        have h2 : ({(a, n - a), (n - a, a)} : Finset (ℕ × ℕ)).card ≤ 2 := Finset.card_le_two
        omega
