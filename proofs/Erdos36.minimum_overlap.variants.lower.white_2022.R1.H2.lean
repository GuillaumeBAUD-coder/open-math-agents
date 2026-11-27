import OMAReductions.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1

-- Step Erdos36.minimum_overlap.variants.lower.white_2022.R1.H2: hypothesis H2 of reduction Erdos36.minimum_overlap.variants.lower.white_2022.R1
-- Credit: @ivillar
-- The tent sum only sees the two differences floor(y) and floor(y)+1, with weights 1-t and t that add up to 1, and each difference class is one overlap count.

open OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1

theorem OMA.solution : OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.H2 := by
  intro A B y
  have hθ0 : (0 : ℝ) ≤ y - ⌊y⌋ := sub_nonneg.mpr (Int.floor_le y)
  have hθ1 : y - ⌊y⌋ < 1 := by linarith [Int.lt_floor_add_one y]
  have hov : ∀ k : ℤ, (∑ p ∈ A ×ˢ B, (if p.1 - p.2 = k then (1 : ℝ) else 0)) =
      (Erdos36.Overlap A B k : ℝ) := by
    intro k
    rw [Finset.sum_boole]
    unfold Erdos36.Overlap
    congr 2
  have hmax : ∀ k : ℤ, (Erdos36.Overlap A B k : ℝ) ≤ (Erdos36.MaxOverlap A B : ℝ) := by
    intro k
    have hb : BddAbove (Set.range (Erdos36.Overlap A B)) := by
      refine ⟨A.card, ?_⟩
      rintro x ⟨j, rfl⟩
      exact overlap_le_card A B j
    exact_mod_cast le_ciSup hb k
  have hterm : ∀ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|) ≤
      (1 - (y - ⌊y⌋)) * (if p.1 - p.2 = -⌊y⌋ then (1 : ℝ) else 0) +
        (y - ⌊y⌋) * (if p.1 - p.2 = -⌊y⌋ - 1 then (1 : ℝ) else 0) := by
    intro p _
    by_cases h1 : p.2 - p.1 = ⌊y⌋
    · rw [if_pos (by omega), if_neg (by omega), h1]
      have h3 : ((⌊y⌋ : ℤ) : ℝ) - y = -(y - ⌊y⌋) := by ring
      rw [h3, abs_neg, abs_of_nonneg hθ0, mul_one, mul_zero, add_zero]
      exact max_le (by linarith) le_rfl
    · by_cases h2 : p.2 - p.1 = ⌊y⌋ + 1
      · rw [if_neg (by omega), if_pos (by omega), h2]
        have h3 : (((⌊y⌋ + 1 : ℤ) : ℤ) : ℝ) - y = 1 - (y - ⌊y⌋) := by push_cast; ring
        rw [h3, abs_of_nonneg (by linarith), mul_zero, mul_one, zero_add]
        exact max_le hθ0 (by linarith)
      · rw [if_neg (by omega), if_neg (by omega), mul_zero, mul_zero, add_zero]
        have h3 : 1 ≤ |((p.2 - p.1 : ℤ) : ℝ) - y| := by
          rcases lt_or_gt_of_ne h1 with h | h
          · have h4 : ((p.2 - p.1 : ℤ) : ℝ) ≤ (⌊y⌋ : ℝ) - 1 := by
              exact_mod_cast (by omega : p.2 - p.1 ≤ ⌊y⌋ - 1)
            rw [abs_of_nonpos (by linarith)]
            linarith
          · have h4 : (⌊y⌋ : ℝ) + 2 ≤ ((p.2 - p.1 : ℤ) : ℝ) := by
              exact_mod_cast (by omega : ⌊y⌋ + 2 ≤ p.2 - p.1)
            rw [abs_of_nonneg (by linarith)]
            linarith
        exact max_le le_rfl (by linarith)
  calc ∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|)
      ≤ ∑ p ∈ A ×ˢ B, ((1 - (y - ⌊y⌋)) * (if p.1 - p.2 = -⌊y⌋ then (1 : ℝ) else 0) +
        (y - ⌊y⌋) * (if p.1 - p.2 = -⌊y⌋ - 1 then (1 : ℝ) else 0)) := Finset.sum_le_sum hterm
    _ = (1 - (y - ⌊y⌋)) * (Erdos36.Overlap A B (-⌊y⌋) : ℝ) +
        (y - ⌊y⌋) * (Erdos36.Overlap A B (-⌊y⌋ - 1) : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hov, hov]
    _ ≤ (1 - (y - ⌊y⌋)) * (Erdos36.MaxOverlap A B : ℝ) +
        (y - ⌊y⌋) * (Erdos36.MaxOverlap A B : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left (hmax _) (by linarith))
          (mul_le_mul_of_nonneg_left (hmax _) hθ0)
    _ = (Erdos36.MaxOverlap A B : ℝ) := by ring
