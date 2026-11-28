import OMAReductions.R_Erdos1132_erdos_1132_parts_i_R1

-- Step Erdos1132.erdos_1132.parts.i.R1.H2: hypothesis H2 of reduction Erdos1132.erdos_1132.parts.i.R1
-- Credit: @luciusacarr
-- Baire category: the sets {t | ∃ n ≥ m, -k < f n t} are open and dense in the Baire space
-- (-1, 1), so their intersection is nonempty; any point in it works with C = -k.

theorem OMA.solution : OMA.R_Erdos1132_erdos_1132_parts_i_R1.H2 := by
  intro f hf hd
  obtain ⟨k, hk⟩ := hd
  haveI : BaireSpace {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} := isOpen_Ioo.baireSpace
  haveI : Nonempty {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} := ⟨⟨0, by norm_num⟩⟩
  have hopen : ∀ m : ℕ, IsOpen {t : {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} |
      ∃ n : ℕ, m ≤ n ∧ -(k : ℝ) < f n t.1} := by
    intro m
    have : {t : {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} | ∃ n : ℕ, m ≤ n ∧ -(k : ℝ) < f n t.1} =
        ⋃ n : ℕ, ⋃ _ : m ≤ n, {t | -(k : ℝ) < f n t.1} := by
      ext t; simp
    rw [this]
    exact isOpen_iUnion fun n => isOpen_iUnion fun _ =>
      isOpen_lt continuous_const ((hf n).comp continuous_subtype_val)
  obtain ⟨t, ht⟩ := (dense_iInter_of_isOpen_nat hopen hk).nonempty
  rw [Set.mem_iInter] at ht
  exact ⟨t.1, t.2, -(k : ℝ), Filter.frequently_atTop.2 fun m => ht m⟩
