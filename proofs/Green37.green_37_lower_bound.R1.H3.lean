import OMAReductions.R_Green37_green_37_lower_bound_R1

/-!
Credit: Hanan Beer (@hananzlt).
Positive one-term covers and the ordered-pair lower bound for two-term covers.
This discharges H3 of the reduction by @estebanlearns.
-/

namespace OMA.Green37BaseBounds

lemma covers_nonempty (N k : ℕ) :
    {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k}.Nonempty := by
  refine ⟨k * N + 1, Finset.range (k * N + 1), Finset.card_range _, ?_⟩
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
  · ext x; simp

lemma minimum_witness (N k : ℕ) :
    ∃ A : Finset ℕ, A.card = Green37.m N k ∧ Green37.IsAPCover (A : Set ℕ) N k := by
  exact Nat.sInf_mem (covers_nonempty N k)

lemma one_lower (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Green37.m N 1 := by
  obtain ⟨A, hcard, hA⟩ := minimum_witness N 1
  obtain ⟨a, s, hsA, _, hs⟩ := hA 1 ⟨le_rfl, hN⟩
  have ha : a ∈ A := by
    apply hsA
    rw [hs]
    exact ⟨0, by norm_num, by simp⟩
  rw [← hcard]
  exact Finset.card_pos.mpr ⟨a, ha⟩

lemma cover_two_lower (A : Finset ℕ) (N : ℕ)
    (hA : Green37.IsAPCover (A : Set ℕ) N 2) :
    2 * N ≤ A.card * (A.card - 1) := by
  have hsub : Finset.Icc 1 N ⊆
      (((A ×ˢ A).filter fun p ↦ p.1 < p.2).image fun p ↦ p.2 - p.1) := by
    intro d hd
    have hd' := Finset.mem_Icc.mp hd
    obtain ⟨a, s, hsA, _, hs⟩ := hA d hd'
    have ha : a ∈ A := by
      apply hsA
      rw [hs]
      exact ⟨0, by norm_num, by simp⟩
    have had : a + d ∈ A := by
      apply hsA
      rw [hs]
      exact ⟨1, by norm_num, by simp⟩
    apply Finset.mem_image.mpr
    refine ⟨(a, a + d), ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, had⟩, by dsimp; omega⟩
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_image_le (s := (A ×ˢ A).filter fun p ↦ p.1 < p.2) (f := fun p ↦ p.2 - p.1))
  rw [Finset.card_product_filter_lt, Nat.choose_two_right] at hcard
  simp only [Nat.card_Icc] at hcard
  omega

end OMA.Green37BaseBounds

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  constructor
  · exact OMA.Green37BaseBounds.one_lower
  · intro N
    obtain ⟨A, hcard, hA⟩ := OMA.Green37BaseBounds.minimum_witness N 2
    rw [← hcard]
    exact OMA.Green37BaseBounds.cover_two_lower A N hA
