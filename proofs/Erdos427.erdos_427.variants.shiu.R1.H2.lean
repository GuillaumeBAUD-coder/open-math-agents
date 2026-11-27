import OMAReductions.R_Erdos427_erdos_427_variants_shiu_R1

-- Step Erdos427.erdos_427.variants.shiu.R1.H2: hypothesis H2 of reduction Erdos427.erdos_427.variants.shiu.R1
-- Credit: @marcusbuffett
-- H2 := ∀ (good : ℕ → Bool) (l r k : ℕ), 1 ≤ k →     (k - 1) * (((Finset.Ico l r).filter (fun i => good i = false)).card + 1) <         ((Finset.Ico l r).filter (fun i => good i = true)).card →     ∃ m : ℕ, l ≤ m ∧ m + k ≤ r ∧ ∀ i ∈ Finset.Ico m (m + k), good i = true

open Finset

theorem OMA.solution : OMA.R_Erdos427_erdos_427_variants_shiu_R1.H2 := by
  intro good l r k hk hexcess
  by_contra hrun
  have hlr : l ≤ r := by
    by_contra! h
    simp [Ico_eq_empty_of_le h.le] at hexcess
  let count (b : Bool) (j : ℕ) := ((Ico l j).filter fun i => good i = b).card
  have bound (j : ℕ) (hl : l ≤ j) (hr : j ≤ r) :
      ∃ s, l ≤ s ∧ s ≤ j ∧ j - s < k ∧ (∀ i ∈ Ico s j, good i = true) ∧
        count true j ≤ (k-1) * count false j + (j-s) := by
    induction j, hl using Nat.le_induction with
    | base => exact ⟨l, le_rfl, le_rfl, by omega, by simp, by simp [count]⟩
    | succ j hj ih =>
      obtain ⟨s, hs, hsj, hlen, hgood, hcount⟩ := ih (by omega)
      have he : Ico l (j+1) = insert j (Ico l j) := by
        ext x
        simp only [mem_Ico, mem_insert]
        omega
      have hc (b : Bool) : count b (j+1) = count b j + (if good j = b then 1 else 0) := by
        unfold count
        rw [he, filter_insert]
        split <;> simp_all
      cases h : good j with
      | false =>
        refine ⟨j+1, by omega, le_rfl, by omega, by simp, ?_⟩
        simp only [hc, h, Bool.false_eq_true, ↓reduceIte, add_zero, mul_add, mul_one,
          Nat.sub_self]
        omega
      | true =>
        have hgood' : ∀ i ∈ Ico s (j+1), good i = true := by
          intro i hi
          by_cases e : i = j
          · simpa [e] using h
          · exact hgood _ (mem_Ico.mpr ⟨(mem_Ico.mp hi).1, by have := (mem_Ico.mp hi).2; omega⟩)
        have hshort : j+1-s < k := by
          by_contra! hlong
          exact hrun ⟨s, hs, by omega, fun i hi => hgood' i
            (mem_Ico.mpr ⟨(mem_Ico.mp hi).1, by have := (mem_Ico.mp hi).2; omega⟩)⟩
        refine ⟨s, hs, by omega, hshort, hgood', ?_⟩
        simp [hc, h]
        omega
  obtain ⟨s, _, _, hlen, _, h⟩ := bound r hlr le_rfl
  change (k-1)*(count false r + 1) < count true r at hexcess
  rw [mul_add, mul_one] at hexcess
  omega
