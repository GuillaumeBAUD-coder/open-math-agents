import OMAReductions.R_Green37_green_37_lower_bound_R1

namespace OMA.GreenPairs

open Finset

theorem minimizer (N k : ℕ) :
    ∃ A : Finset ℕ, A.card = Green37.m N k ∧ Green37.IsAPCover (A : Set ℕ) N k := by
  let S : Set ℕ := {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k}
  have hS : S.Nonempty := by
    refine ⟨k * N + 1, range (k * N + 1), card_range _, ?_⟩
    intro d hd
    refine ⟨0, ((range k).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      simp only [mem_coe, mem_range] at hi ⊢
      exact Nat.lt_succ_of_le (Nat.mul_le_mul hi.le hd.2)
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        card_image_of_injective _ (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h),
        card_range]
    · ext x
      simp
  exact Nat.sInf_mem hS

end OMA.GreenPairs

open Finset

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  classical
  constructor
  · intro N hN
    obtain ⟨A, hc, hA⟩ := OMA.GreenPairs.minimizer N 1
    obtain ⟨a, T, hT, _, he⟩ := hA 1 ⟨by decide, hN⟩
    have ha : a ∈ T := by
      rw [he]
      exact ⟨0, by decide, by simp⟩
    rw [← hc]
    exact Finset.card_pos.mpr ⟨a, hT ha⟩
  · intro N
    obtain ⟨A, hc, hA⟩ := OMA.GreenPairs.minimizer N 2
    have pairs (d : ℕ) (hd : d ∈ Icc 1 N) : ∃ a, a ∈ A ∧ a + d ∈ A := by
      obtain ⟨a, T, hT, _, he⟩ := hA d (mem_Icc.mp hd)
      refine ⟨a, hT ?_, hT ?_⟩
      · rw [he]
        exact ⟨0, by decide, by simp⟩
      · rw [he]
        exact ⟨1, by decide, by simp⟩
    choose! a ha ha' using pairs
    let f : ℕ × Bool → ℕ × ℕ := fun t =>
      if t.2 then (a t.1 + t.1, a t.1) else (a t.1, a t.1 + t.1)
    let D := Icc 1 N ×ˢ (univ : Finset Bool)
    have hmaps : Set.MapsTo f (D : Set (ℕ × Bool)) (A.offDiag : Set (ℕ × ℕ)) := by
      rintro ⟨d, b⟩ h
      have hd : d ∈ Icc 1 N := (mem_product.mp h).1
      have hp := (mem_Icc.mp hd).1
      have h₁ := ha d hd
      have h₂ := ha' d hd
      change f (d, b) ∈ A.offDiag
      cases b <;> simp [f, Finset.mem_offDiag, h₁, h₂] <;> omega
    have hinj : Set.InjOn f (D : Set (ℕ × Bool)) := by
      rintro ⟨d, b⟩ h ⟨e, c⟩ h' he
      have hd : 1 ≤ d := (mem_Icc.mp (mem_product.mp h).1).1
      have he' : 1 ≤ e := (mem_Icc.mp (mem_product.mp h').1).1
      cases b <;> cases c <;> simp [f] at he ⊢ <;> omega
    have hcard := Finset.card_le_card_of_injOn f hmaps hinj
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    simpa [D, Finset.card_product, Nat.card_Icc, Finset.offDiag_card, hc, Nat.mul_comm] using hcard
