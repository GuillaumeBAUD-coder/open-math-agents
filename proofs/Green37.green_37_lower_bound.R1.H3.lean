import OMAReductions.R_Green37_green_37_lower_bound_R1

namespace OMA.APCoverBounds

lemma witness (N k : ℕ) : ∃ A : Finset ℕ,
    A.card = Green37.m N k ∧ Green37.IsAPCover (A : Set ℕ) N k := by
  change sInf {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k} ∈
    {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k}
  apply Nat.sInf_mem
  refine ⟨k*N+1, Finset.range (k*N+1), Finset.card_range _, ?_⟩
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i => i*d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_right hd.1 h),
      Finset.card_range]
  · ext x
    simp

lemma pair_bound (N : ℕ) (A : Finset ℕ)
    (hcover : Green37.IsAPCover (A : Set ℕ) N 2) :
    2*N ≤ A.card * (A.card-1) := by
  classical
  have hw : ∀ d ∈ Finset.Icc 1 N, ∃ a, a ∈ A ∧ a+d ∈ A := by
    intro d hd
    obtain ⟨a, s, hsA, _, hs⟩ := hcover d (Finset.mem_Icc.mp hd)
    refine ⟨a, hsA ?_, hsA ?_⟩
    · rw [hs]
      exact ⟨0, by norm_num, by simp⟩
    · rw [hs]
      exact ⟨1, by norm_num, by simp⟩
  choose! a ha using hw
  let B := Finset.Icc 1 N ×ˢ (Finset.univ : Finset Bool)
  let f : ℕ × Bool → ℕ × ℕ := fun x =>
    if x.2 then (a x.1 + x.1, a x.1) else (a x.1, a x.1+x.1)
  have hmaps : ∀ x ∈ B, f x ∈ A.offDiag := by
    rintro ⟨d, b⟩ hd
    have hdI := (Finset.mem_product.mp hd).1
    have hd0 := (Finset.mem_Icc.mp hdI).1
    have H := ha d hdI
    cases b <;> simp only [f, Bool.false_eq_true, ↓reduceIte, Finset.mem_offDiag] <;>
      exact ⟨by tauto, by tauto, by omega⟩
  have hinj : Set.InjOn f (B : Set (ℕ × Bool)) := by
    rintro ⟨d, b⟩ hd ⟨e, c⟩ he hij
    have hd0 := (Finset.mem_Icc.mp (Finset.mem_product.mp hd).1).1
    have he0 := (Finset.mem_Icc.mp (Finset.mem_product.mp he).1).1
    cases b <;> cases c <;> simp only [f, Bool.false_eq_true, ↓reduceIte,
      Prod.mk.injEq, and_true] at hij ⊢ <;> omega
  have hc := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.offDiag_card, ← Nat.mul_sub_one] at hc
  simpa only [B, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel,
    Finset.card_univ, Fintype.card_bool, mul_comm] using hc

end OMA.APCoverBounds

-- Step Green37.green_37_lower_bound.R1.H3: hypothesis H3 of reduction Green37.green_37_lower_bound.R1
-- Credit: @DeepDuke
-- H3 := (∀ N : ℕ, 1 ≤ N → 1 ≤ Green37.m N 1) ∧   (∀ N : ℕ, 2 * N ≤ Green37.m N 2 * (Green37.m N 2 - 1))

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  constructor
  · intro N hN
    obtain ⟨A, hc, hcov⟩ := OMA.APCoverBounds.witness N 1
    obtain ⟨a, s, hsA, _, hs⟩ := hcov 1 ⟨le_rfl, hN⟩
    have ha : a ∈ A := hsA (by rw [hs]; exact ⟨0, by norm_num, by simp⟩)
    rw [← hc]
    exact Finset.card_pos.mpr ⟨a, ha⟩
  · intro N
    obtain ⟨A, hc, hcov⟩ := OMA.APCoverBounds.witness N 2
    rw [← hc]
    exact OMA.APCoverBounds.pair_bound N A hcov

