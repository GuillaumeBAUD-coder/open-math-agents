import OMAStatements.S_oeis_a057030

open OMA.S_oeis_a057030

theorem bc_a057030_sp (m f i : ℕ) :
    sourcePosition m (f + 1) (i + 1) = sourcePosition m f i + 1 := by
  unfold sourcePosition
  by_cases h : i < f
  · have h' : i + 1 < f + 1 := by omega
    rw [if_pos h', if_pos h]
  · have h' : ¬ (i + 1 < f + 1) := by omega
    rw [if_neg h', if_neg h]
    have e : i + 1 - (f + 1) = i - f := by omega
    rw [e]
    first
    | omega
    | ring

theorem bc_a057030_shift (r : ℕ) : ∀ i : ℕ, afterStages 1 r (i + 1) = afterStages 0 r i + 1 := by
  induction r with
  | zero =>
    intro i
    rfl
  | succ r ih =>
    intro i
    show afterStages 1 r (sourcePosition (r + 2) (r + 1 + 1) (i + 1)) =
      afterStages 0 r (sourcePosition (r + 2) (r + 1) i) + 1
    rw [bc_a057030_sp (r + 2) (r + 1) i, ih]

theorem OMA.solution : type_of% @OMA.S_oeis_a057030.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hc : k + 1 < k + 1 + 1 + 1 := by omega
  have hs : sourcePosition (k + 1 + 2) (k + 1 + 1 + 1) (k + 1) = k + 1 := by
    unfold sourcePosition
    rw [if_pos hc]
  have h1 : afterStages 1 (k + 1 + 1) (k + 1) = afterStages 0 (k + 1) k + 1 := by
    rw [show afterStages 1 (k + 1 + 1) (k + 1) =
        afterStages 1 (k + 1) (sourcePosition (k + 1 + 2) (k + 1 + 1 + 1) (k + 1)) from rfl, hs]
    exact bc_a057030_shift (k + 1) k
  show afterStages 0 (k + 1) k = afterStages 1 (k + 1 + 1) (k + 1) - 1
  omega
