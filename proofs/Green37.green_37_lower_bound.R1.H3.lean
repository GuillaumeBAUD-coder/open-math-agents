import OMAReductions.R_Green37_green_37_lower_bound_R1
import Mathlib.Tactic

/-! Proof of step H3 of Green37.green_37_lower_bound.R1 -/

-- Credit: @nijv

lemma green37_cover_nonempty (N k : ℕ) :
    { m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k }.Nonempty := by
  refine ⟨k * N + 1, Finset.range (k * N + 1), Finset.card_range _, ?_⟩
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i => i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h => Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
  · ext x; simp

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  unfold OMA.R_Green37_green_37_lower_bound_R1.H3
  constructor
  · intro N hN
    obtain ⟨A, hAcard, hAcov⟩ := Nat.sInf_mem (green37_cover_nonempty N 1)
    unfold Green37.m
    rw [← hAcard]
    obtain ⟨a, s, hsA, hsap⟩ := hAcov 1 ⟨le_rfl, hN⟩
    have ha : a ∈ s := by
      rw [hsap.2]
      exact ⟨0, by norm_num, by simp⟩
    exact Finset.card_pos.mpr ⟨a, hsA ha⟩
  · intro N
    obtain ⟨A, hAcard, hAcov⟩ := Nat.sInf_mem (green37_cover_nonempty N 2)
    unfold Green37.m
    rw [← hAcard]
    let φ : ℕ × ℕ → Bool × ℕ := fun p =>
      (decide (p.1 < p.2), if p.1 < p.2 then p.2 - p.1 else p.1 - p.2)
    have hsub : (({true, false} : Finset Bool) ×ˢ Finset.Icc 1 N) ⊆ A.offDiag.image φ := by
      rintro ⟨b, d⟩ hbd
      simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hbd
      obtain ⟨hb, hd1, hdN⟩ := hbd
      obtain ⟨a, s, hsA, hsap⟩ := hAcov d ⟨hd1, hdN⟩
      have ha0 : a ∈ A := hsA (by rw [hsap.2]; exact ⟨0, by norm_num, by simp⟩)
      have ha1 : a + d ∈ A := hsA (by rw [hsap.2]; exact ⟨1, by norm_num, by simp⟩)
      rcases hb with rfl | rfl
      · refine Finset.mem_image.mpr ⟨(a, a + d), ?_, ?_⟩
        · exact Finset.mem_offDiag.mpr ⟨ha0, ha1, by omega⟩
        · simp only [φ]
          have hlt : a < a + d := by omega
          simp [hlt]
      · refine Finset.mem_image.mpr ⟨(a + d, a), ?_, ?_⟩
        · exact Finset.mem_offDiag.mpr ⟨ha1, ha0, by omega⟩
        · simp only [φ]
          have hlt : ¬ (a + d < a) := by omega
          simp [hlt]
    have hcard1 : (({true, false} : Finset Bool) ×ˢ Finset.Icc 1 N).card = 2 * N := by
      rw [Finset.card_product]
      simp [Nat.card_Icc]
    have hcard2 : (A.offDiag.image φ).card ≤ A.offDiag.card := Finset.card_image_le
    have hcard3 : A.offDiag.card = A.card * (A.card - 1) := by
      rw [Finset.offDiag_card]
      rcases A.card with _ | k <;> simp [Nat.succ_mul, Nat.mul_succ]
    have hle := Finset.card_le_card hsub
    omega
