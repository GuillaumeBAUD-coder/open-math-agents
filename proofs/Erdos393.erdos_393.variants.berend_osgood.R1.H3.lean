import OMAReductions.R_Erdos393_erdos_393_variants_berend_osgood_R1
import Mathlib

-- Step Erdos393.erdos_393.variants.berend_osgood.R1.H3: hypothesis H3 of reduction
-- Erdos393.erdos_393.variants.berend_osgood.R1
-- Credit: @ivillar. Unfold the minimum f n (attained for n >= 2) and translate its factor set by a.

/-! A minimal factorisation of n! translated to start at 0. -/

open Finset Filter Erdos393
open scoped Nat Topology

namespace P7E393

theorem f_mem (n : ℕ) (hn : 2 ≤ n) :
    f n ∈ {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
      ∏ i ∈ s, i = n !} := by
  have hprod : ∏ i ∈ Finset.Ico 1 (n + 1), i = n ! := Finset.prod_Ico_id_eq_factorial n
  apply Nat.sInf_mem
  refine ⟨n - 1, by omega, 1, Finset.Ico 1 (n + 1), ?_, ?_, ?_, hprod⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    exact Finset.mem_Icc.2 ⟨h1, by omega⟩
  · exact Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  · exact Finset.mem_Ico.2 ⟨by omega, by omega⟩

end P7E393

theorem OMA.solution : OMA.R_Erdos393_erdos_393_variants_berend_osgood_R1.H3 := by
  unfold OMA.R_Erdos393_erdos_393_variants_berend_osgood_R1.H3
  intro n hn
  obtain ⟨hm, a, s, hs, ha, hb, hprod⟩ := P7E393.f_mem n hn
  have hge : ∀ x ∈ s, a ≤ x ∧ x ≤ a + f n := fun x hx => Finset.mem_Icc.1 (hs hx)
  have hinj : Set.InjOn (fun x => x - a) (s : Set ℕ) := by
    intro x hx y hy hxy
    have := hge x hx
    have := hge y hy
    simp only at hxy
    omega
  refine ⟨s.image (fun x => x - a), ?_, ?_, a, ?_⟩
  · intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    have := hge x hx
    exact Finset.mem_range.2 (by omega)
  · rw [Finset.card_image_of_injOn hinj]
    have hne : a ≠ a + f n := by omega
    calc 2 = ({a, a + f n} : Finset ℕ).card := (Finset.card_pair hne).symm
      _ ≤ s.card := Finset.card_le_card (by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact ha
          · rw [Finset.mem_singleton.1 hx]; exact hb)
  · rw [Finset.prod_image hinj, ← hprod]
    apply Finset.prod_congr rfl
    intro x hx
    have := hge x hx
    omega

