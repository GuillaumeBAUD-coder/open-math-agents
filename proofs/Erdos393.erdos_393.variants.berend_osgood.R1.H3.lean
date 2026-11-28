import OMAReductions.R_Erdos393_erdos_393_variants_berend_osgood_R1
import Mathlib

-- Step Erdos393.erdos_393.variants.berend_osgood.R1.H3: hypothesis H3 of reduction Erdos393.erdos_393.variants.berend_osgood.R1
-- Credit: @Raimo33

open scoped Nat

theorem OMA.solution : OMA.R_Erdos393_erdos_393_variants_berend_osgood_R1.H3 := by
  intro n hn
  have hne : ({m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
      ∏ i ∈ s, i = n !}).Nonempty := by
    refine ⟨n - 1, by omega, 1, Finset.Icc 1 n, ?_, ?_, ?_, ?_⟩
    · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
    · simp only [Finset.mem_Icc]; omega
    · simp only [Finset.mem_Icc]; omega
    · rw [← Finset.prod_Ico_id_eq_factorial]
      rfl
  have hmem : Erdos393.f n ∈ {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
      ∏ i ∈ s, i = n !} := Nat.sInf_mem hne
  obtain ⟨hm1, a, s, hs, ha, ham, hprod⟩ := hmem
  refine ⟨s.image (fun x => x - a), ?_, ?_, a, ?_⟩
  · intro i hi
    simp only [Finset.mem_image] at hi
    obtain ⟨x, hx, rfl⟩ := hi
    have := hs hx
    simp only [Finset.mem_Icc] at this
    simp only [Finset.mem_range]
    omega
  · have hinj : Set.InjOn (fun x => x - a) (s : Set ℕ) := by
      intro x hx y hy hxy
      have h1 := hs hx; have h2 := hs hy
      simp only [Finset.mem_Icc] at h1 h2
      simp only at hxy
      omega
    rw [Finset.card_image_of_injOn hinj]
    have : ({a, a + Erdos393.f n} : Finset ℕ) ⊆ s := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact ham
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair (by omega : a ≠ a + Erdos393.f n)] at h2
    exact h2
  · rw [Finset.prod_image]
    · rw [← hprod]
      apply Finset.prod_congr rfl
      intro x hx
      have := hs hx
      simp only [Finset.mem_Icc] at this
      omega
    · intro x hx y hy hxy
      have h1 := hs hx; have h2 := hs hy
      simp only [Finset.mem_Icc] at h1 h2
      simp only at hxy
      omega
