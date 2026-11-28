import OMAReductions.R_VizingConjecture_vizing_conjecture_R1

/-!
# Proof of `VizingConjecture.vizing_conjecture.R1.H1`

Vizing's conjecture when one factor has domination number at most one.
-/

-- Step VizingConjecture.vizing_conjecture.R1.H1: hypothesis H1 of reduction VizingConjecture.vizing_conjecture.R1
-- Credit: @LiJiaHua1024

open SimpleGraph

theorem OMA.solution : OMA.R_VizingConjecture_vizing_conjecture_R1.H1 := by
  intro α β _ _ _ _ G H hle
  rcases hle with hG | hH
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hG with hG0 | hG1
    · simp [hG0]
    · have hne : Nonempty α := by
        by_contra h
        rw [not_nonempty_iff] at h
        have : G.dominationNumber = 0 :=
          Nat.le_zero.mp (dominationNumber_le_of_isDominating G ∅ (fun v => (IsEmpty.false v).elim))
        omega
      rw [hG1, one_mul]
      obtain ⟨D, hD, hcard⟩ := exists_isNDominatingSet_dominationNumber (G □ H)
      refine le_trans (dominationNumber_le_of_isDominating H (D.image Prod.snd) ?_) ?_
      · intro b
        obtain ⟨a⟩ := hne
        rcases hD (a, b) with h | ⟨⟨u, c⟩, hu, hadj⟩
        · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp h)))
        · rw [boxProd_adj] at hadj
          rcases hadj with ⟨-, hbc⟩ | ⟨hbc, -⟩
          · obtain rfl : b = c := hbc
            exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hu)))
          · exact Or.inr ⟨c, Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hu)), hbc⟩
      · exact hcard ▸ Finset.card_image_le
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hH with hH0 | hH1
    · simp [hH0]
    · exact VizingConjecture.vizing_conjecture.variants.dominationNumber_eq_one G H hH1
