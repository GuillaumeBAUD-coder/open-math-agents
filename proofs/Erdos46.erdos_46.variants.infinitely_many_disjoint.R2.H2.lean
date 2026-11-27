import OMAReductions.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2

-- Step Erdos46.erdos_46.variants.infinitely_many_disjoint.R2.H2: hypothesis H2 of reduction Erdos46.erdos_46.variants.infinitely_many_disjoint.R2
-- Credit: @ivillar
-- The cutoff recursion follows `disjoint_of_one` in the merged reduction
-- Erdos46.erdos_46.variants.infinitely_many_disjoint.R1 by @WillyNilsson (PR #4868).

theorem OMA.solution : OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2.H2 := by
  intro P hP
  choose S hPS fresh using hP
  let cutoff : ℕ → ℕ := Nat.rec 0 (fun _ b => max b ((S b).sup id))
  have step (i : ℕ) : cutoff (i + 1) = max (cutoff i) ((S (cutoff i)).sup id) := rfl
  have mono : Monotone cutoff := monotone_nat_of_le_succ fun i => by
    rw [step]; exact le_max_left _ _
  have sep {i j : ℕ} (hij : i < j) : Disjoint (S (cutoff i)) (S (cutoff j)) := by
    apply Finset.disjoint_left.mpr
    intro n hi hj
    have hn : n ≤ (S (cutoff i)).sup id := Finset.le_sup (f := id) hi
    have upto : (S (cutoff i)).sup id ≤ cutoff (i + 1) := by
      rw [step]; exact le_max_right _ _
    exact (fresh (cutoff j) n hj).not_ge (hn.trans (upto.trans (mono hij)))
  refine ⟨fun i => S (cutoff i), ?_, fun i => hPS _⟩
  intro i j hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact sep h
  · exact (sep h).symm
