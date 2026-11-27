import OMAReductions.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1

-- Step Erdos36.minimum_overlap.variants.lower.white_2022.R1.H2
-- Credit: @caa1982

open Finset

private lemma overlap_le_maxOverlap (A B : Finset ℤ) (k : ℤ) :
    Erdos36.Overlap A B k ≤ Erdos36.MaxOverlap A B := by
  unfold Erdos36.MaxOverlap
  refine le_ciSup ?_ k
  refine ⟨A.card, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.overlap_le_card A B j

private lemma card_filter_sub_eq (A B : Finset ℤ) (m : ℤ) :
    ((A ×ˢ B).filter (fun p : ℤ × ℤ => p.2 - p.1 = m)).card = Erdos36.Overlap A B (-m) := by
  unfold Erdos36.Overlap
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  constructor <;> rintro ⟨h, heq⟩ <;> exact ⟨h, by omega⟩

theorem OMA.solution : OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.H2 := by
  intro A B y
  let m : ℤ := ⌊y⌋
  let t : ℝ := y - (m : ℝ)
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Int.floor_le y)
  have ht1 : t < 1 := by
    have := Int.lt_floor_add_one y
    dsimp only [t, m]
    linarith
  let S0 := (A ×ˢ B).filter (fun p : ℤ × ℤ => p.2 - p.1 = m)
  let S1 := (A ×ˢ B).filter (fun p : ℤ × ℤ => p.2 - p.1 = m + 1)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro p h0 h1
    have hp0 := (Finset.mem_filter.mp h0).2
    have hp1 := (Finset.mem_filter.mp h1).2
    omega
  have hsub : S0 ∪ S1 ⊆ A ×ˢ B :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsum_eq :
      ∑ p ∈ A ×ˢ B, max (0 : ℝ) (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|) =
      ∑ p ∈ S0 ∪ S1, max (0 : ℝ) (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|) := by
    symm
    apply Finset.sum_subset hsub
    intro p hp hpU
    simp only [Finset.mem_union, S0, S1, Finset.mem_filter, hp, true_and, not_or] at hpU
    have hd : p.2 - p.1 ≤ m - 1 ∨ m + 2 ≤ p.2 - p.1 := by omega
    have habs : 1 ≤ |((p.2 - p.1 : ℤ) : ℝ) - y| := by
      rcases hd with h | h
      · have hR : ((p.2 - p.1 : ℤ) : ℝ) ≤ (m : ℝ) - 1 := by exact_mod_cast h
        rw [abs_of_nonpos (by linarith : ((p.2 - p.1 : ℤ) : ℝ) - y ≤ 0)]
        linarith
      · have hR : (m : ℝ) + 2 ≤ ((p.2 - p.1 : ℤ) : ℝ) := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith : 0 ≤ ((p.2 - p.1 : ℤ) : ℝ) - y)]
        linarith
    exact max_eq_left (by linarith)
  rw [hsum_eq, Finset.sum_union hdisj]
  have hS0 : ∑ p ∈ S0, max (0 : ℝ) (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|) = (S0.card : ℝ) * (1 - t) := by
    have hconst : ∀ p ∈ S0, max (0 : ℝ) (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|) = 1 - t := by
      intro p hp
      have heq : ((p.2 - p.1 : ℤ) : ℝ) = (m : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
      rw [heq, show (m : ℝ) - y = -t by dsimp only [t]; ring, abs_neg, abs_of_nonneg ht0]
      exact max_eq_right (by linarith)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hS1 : ∑ p ∈ S1, max (0 : ℝ) (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|) = (S1.card : ℝ) * t := by
    have hconst : ∀ p ∈ S1, max (0 : ℝ) (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|) = t := by
      intro p hp
      have heq : ((p.2 - p.1 : ℤ) : ℝ) = (m : ℝ) + 1 := by exact_mod_cast (Finset.mem_filter.mp hp).2
      rw [heq, show (m : ℝ) + 1 - y = 1 - t by dsimp only [t]; ring, abs_of_nonneg (by linarith)]
      have : 1 - (1 - t) = t := by ring
      rw [this]
      exact max_eq_right ht0
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [hS0, hS1]
  have hle0 : (S0.card : ℝ) ≤ (Erdos36.MaxOverlap A B : ℝ) := by
    exact_mod_cast (card_filter_sub_eq A B m ▸ overlap_le_maxOverlap A B (-m))
  have hle1 : (S1.card : ℝ) ≤ (Erdos36.MaxOverlap A B : ℝ) := by
    exact_mod_cast (card_filter_sub_eq A B (m + 1) ▸ overlap_le_maxOverlap A B (-(m + 1)))
  nlinarith
