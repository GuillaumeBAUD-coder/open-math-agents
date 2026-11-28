import OMAReductions.R_Erdos393_erdos_393_R1
import Mathlib

-- Step Erdos393.erdos_393.R1.H3: hypothesis H3 of reduction Erdos393.erdos_393.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! For `n ≥ 2` the set defining `f n` is nonempty (`n! = 1 * 2 * ... * n`), so its infimum
`f n` is attained by a factor set `s ⊆ [a, a + f n]` containing `a` and `a + f n`. Translating by
`-a` gives `T ⊆ {0, ..., f n}` with `∏ i ∈ T, (a + i) = n!`, and `|T| = |s| ≥ 2` because
`f n ≥ 1`. -/

open Finset Filter Erdos393
open scoped Nat Topology

theorem OMA.solution : OMA.R_Erdos393_erdos_393_R1.H3 := by
  intro n hn
  have hne : {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
      ∏ i ∈ s, i = n !}.Nonempty := by
    refine ⟨n - 1, by omega, 1, Finset.Ico 1 (n + 1), ?_, ?_, ?_,
      Finset.prod_Ico_id_eq_factorial n⟩
    · intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
      exact Finset.mem_Icc.2 ⟨h1, by omega⟩
    · exact Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    · exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  obtain ⟨hm1, a, s, hs, has, hams, hprod⟩ := Nat.sInf_mem hne
  change 1 ≤ f n at hm1
  change s ⊆ Finset.Icc a (a + f n) at hs
  change a + f n ∈ s at hams
  have hge : ∀ x ∈ s, a ≤ x := fun x hx => (Finset.mem_Icc.mp (hs hx)).1
  have hinj : Set.InjOn (fun x => x - a) (s : Set ℕ) := by
    intro x hx y hy hxy
    have := hge x hx
    have := hge y hy
    simp only at hxy
    omega
  refine ⟨s.image (fun x => x - a), ?_, ?_, a, ?_⟩
  · intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    have := Finset.mem_Icc.mp (hs hx)
    exact Finset.mem_range.mpr (by omega)
  · rw [Finset.card_image_of_injOn hinj]
    have hpair : {a, a + f n} ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact has
      · rw [Finset.mem_singleton.mp hx]; exact hams
    have := Finset.card_le_card hpair
    rwa [Finset.card_pair (by omega)] at this
  · rw [Finset.prod_image hinj, ← hprod]
    apply Finset.prod_congr rfl
    intro x hx
    have := hge x hx
    omega
