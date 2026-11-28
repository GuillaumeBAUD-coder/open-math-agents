import OMAReductions.R_VizingConjecture_vizing_conjecture_R1

-- Vizing's conjecture when one of the two graphs has domination number at most one.
-- If D dominates the Cartesian product of G and H and G has a vertex a, then the projection of D to H
-- dominates H: the vertex (a, b) is in D or adjacent to some w in D, and then b is the second coordinate of w
-- or adjacent to it. So the domination number of the product is at least that of H, and likewise of G.
-- This is the trivial classical case, not progress on the conjecture.

open SimpleGraph

namespace OMA.Vizing1

theorem dom_exists {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) :
    ∃ D : Finset α, G.IsDominating (D : Set α) ∧ D.card = G.dominationNumber := by
  have hne : {n | ∃ D : Finset α, G.IsNDominatingSet n D}.Nonempty :=
    ⟨(Finset.univ : Finset α).card, Finset.univ, ⟨fun v => Or.inl (by simp), rfl⟩⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  exact ⟨D, hD.isDominating, hD.card_eq⟩

theorem dom_le {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) (D : Finset α)
    (hD : G.IsDominating (D : Set α)) : G.dominationNumber ≤ D.card :=
  Nat.sInf_le ⟨D, ⟨hD, rfl⟩⟩

theorem dom_empty {α : Type} [Fintype α] [DecidableEq α] [IsEmpty α] (G : SimpleGraph α) :
    G.dominationNumber = 0 := by
  have h := dom_le G ∅ (fun v => isEmptyElim v)
  simpa using h

theorem snd_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) [Nonempty α] :
    H.dominationNumber ≤ (G □ H).dominationNumber := by
  obtain ⟨D, hD, hc⟩ := dom_exists (G □ H)
  obtain ⟨a⟩ := ‹Nonempty α›
  have hdom : H.IsDominating ((D.image Prod.snd : Finset β) : Set β) := by
    intro b
    rcases hD (a, b) with h | ⟨w, hw, hadj⟩
    · left
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(a, b), h, rfl⟩)
    · rw [SimpleGraph.boxProd_adj] at hadj
      rcases hadj with ⟨_, h2⟩ | ⟨h1, _⟩
      · left
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, h2.symm⟩)
      · right
        exact ⟨w.2, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩), h1⟩
  calc H.dominationNumber ≤ (D.image Prod.snd).card := dom_le H _ hdom
    _ ≤ D.card := Finset.card_image_le
    _ = (G □ H).dominationNumber := hc

theorem fst_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) [Nonempty β] :
    G.dominationNumber ≤ (G □ H).dominationNumber := by
  obtain ⟨D, hD, hc⟩ := dom_exists (G □ H)
  obtain ⟨b⟩ := ‹Nonempty β›
  have hdom : G.IsDominating ((D.image Prod.fst : Finset α) : Set α) := by
    intro a
    rcases hD (a, b) with h | ⟨w, hw, hadj⟩
    · left
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(a, b), h, rfl⟩)
    · rw [SimpleGraph.boxProd_adj] at hadj
      rcases hadj with ⟨h1, _⟩ | ⟨_, h2⟩
      · right
        exact ⟨w.1, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩), h1⟩
      · left
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, h2.symm⟩)
  calc G.dominationNumber ≤ (D.image Prod.fst).card := dom_le G _ hdom
    _ ≤ D.card := Finset.card_image_le
    _ = (G □ H).dominationNumber := hc

theorem small {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β)
    (h : G.dominationNumber ≤ 1 ∨ H.dominationNumber ≤ 1) :
    G.dominationNumber * H.dominationNumber ≤ (G □ H).dominationNumber := by
  rcases h with h | h
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
    · rw [h0, Nat.zero_mul]
      exact Nat.zero_le _
    · rcases isEmpty_or_nonempty α with he | hn
      · rw [dom_empty G] at h1
        omega
      · rw [h1, Nat.one_mul]
        exact snd_le G H
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
    · rw [h0, Nat.mul_zero]
      exact Nat.zero_le _
    · rcases isEmpty_or_nonempty β with he | hn
      · rw [dom_empty H] at h1
        omega
      · rw [h1, Nat.mul_one]
        exact fst_le G H

end OMA.Vizing1

theorem OMA.solution : OMA.R_VizingConjecture_vizing_conjecture_R1.H1 := by
  intro α β _ _ _ _ G H h
  exact OMA.Vizing1.small G H h
