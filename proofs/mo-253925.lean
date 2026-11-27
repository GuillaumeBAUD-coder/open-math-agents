import OMAStatements.S_mo_253925
import Mathlib

namespace OMA.Mo253925

/-- A supergradient at `z` (the right derivative), with slope information. -/
lemma sg {G : ℝ → ℝ} (hG : ConcaveOn ℝ Set.univ G) (z : ℝ) :
    ∃ s : ℝ, (∀ y, G y ≤ G z + s * (y - z)) ∧ (∀ b, z < b → (G b - G z) / (b - z) ≤ s) ∧
      ((∀ b, z < b → G b ≤ G z) → s ≤ 0) := by
  set R : Set ℝ := (fun b => (G b - G z) / (b - z)) '' Set.Ioi z with hR
  have hadj : ∀ a b, a < z → z < b → (G b - G z) / (b - z) ≤ (G z - G a) / (z - a) :=
    fun a b ha hb => hG.slope_anti_adjacent (Set.mem_univ a) (Set.mem_univ b) ha hb
  have hne : R.Nonempty := ⟨_, Set.mem_image_of_mem _ (Set.mem_Ioi.2 (lt_add_one z))⟩
  have hbdd : BddAbove R := by
    refine ⟨(G z - G (z - 1)) / (z - (z - 1)), ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hadj (z - 1) b (by linarith) hb
  have hup : ∀ b, z < b → (G b - G z) / (b - z) ≤ sSup R :=
    fun b hb => le_csSup hbdd (Set.mem_image_of_mem _ hb)
  refine ⟨sSup R, ?_, hup, ?_⟩
  · intro y
    rcases lt_trichotomy y z with h | h | h
    · have h1 : sSup R ≤ (G z - G y) / (z - y) := by
        apply csSup_le hne
        rintro _ ⟨b, hb, rfl⟩
        exact hadj y b h hb
      have h2 : 0 < z - y := by linarith
      rw [le_div_iff₀ h2] at h1
      nlinarith
    · subst h; simp
    · have h1 := hup y h
      have h2 : 0 < y - z := by linarith
      rw [div_le_iff₀ h2] at h1
      linarith
  · intro hall
    apply csSup_le hne
    rintro _ ⟨b, hb, rfl⟩
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hall b hb]) (by linarith [Set.mem_Ioi.1 hb])

lemma pt {G : ℝ → ℝ} (hG : ConcaveOn ℝ Set.univ G) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    ∃ s : ℝ, ∀ y, OMA.S_mo_253925.Geps G ε x + s * (y - x) - ε * |s| ≥ G y := by
  have hcont : ContinuousOn G (Set.Icc (x - ε) (x + ε)) :=
    (hG.continuousOn isOpen_univ).mono (Set.subset_univ _)
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith)) hcont
  have hmax' : ∀ y, x - ε ≤ y → y ≤ x + ε → G y ≤ G z := fun y h1 h2 => hmax ⟨h1, h2⟩
  have hGe : OMA.S_mo_253925.Geps G ε x = G z := by
    unfold OMA.S_mo_253925.Geps
    refine IsGreatest.csSup_eq ⟨Set.mem_image_of_mem _ hz, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  rw [hGe]
  obtain ⟨hz1, hz2⟩ := hz
  -- right of z is below G z unless z is the right endpoint
  have F1 : z < x + ε → ∀ b, z < b → G b ≤ G z := by
    intro hlt b hb
    by_cases hbw : b ≤ x + ε
    · exact hmax' b (by linarith) hbw
    · push_neg at hbw
      have hw := hmax' (x + ε) (by linarith) le_rfl
      have := hG.slope_anti_adjacent (Set.mem_univ z) (Set.mem_univ b) hlt hbw
      rw [div_le_div_iff₀ (by linarith) (by linarith)] at this
      nlinarith
  have F2 : x - ε < z → ∀ a, a < z → G a ≤ G z := by
    intro hlt a ha
    by_cases haw : x - ε ≤ a
    · exact hmax' a haw (by linarith)
    · push_neg at haw
      have hw := hmax' (x - ε) le_rfl (by linarith)
      have := hG.slope_anti_adjacent (Set.mem_univ a) (Set.mem_univ z) haw hlt
      rw [div_le_div_iff₀ (by linarith) (by linarith)] at this
      nlinarith
  by_cases hglob : ∀ y, G y ≤ G z
  · exact ⟨0, fun y => by simpa using hglob y⟩
  obtain ⟨s, hs, hslope, hneg⟩ := sg hG z
  refine ⟨s, fun y => ?_⟩
  have key : ε * |s| ≤ s * (z - x) := by
    by_cases hr : ∀ b, z < b → G b ≤ G z
    · have hs0 := hneg hr
      have hzl : z = x - ε := by
        by_contra hne
        apply hglob
        intro y
        rcases lt_trichotomy y z with h | h | h
        · exact F2 (lt_of_le_of_ne hz1 (Ne.symm hne)) y h
        · rw [h]
        · exact hr y h
      rw [abs_of_nonpos hs0, hzl]; linarith
    · push_neg at hr
      obtain ⟨b, hb, hGb⟩ := hr
      have hzr : z = x + ε := by
        by_contra hne
        exact absurd (F1 (lt_of_le_of_ne hz2 hne) b hb) (not_le.2 hGb)
      have hs0 : 0 < s := lt_of_lt_of_le (div_pos (by linarith) (by linarith)) (hslope b hb)
      rw [abs_of_pos hs0, hzr]; linarith
  have := hs y
  nlinarith

end OMA.Mo253925

theorem OMA.solution : type_of% @OMA.S_mo_253925.main := by
  intro G ε hG hε
  choose h hh using OMA.Mo253925.pt hG hε
  exact ⟨h, hh⟩
