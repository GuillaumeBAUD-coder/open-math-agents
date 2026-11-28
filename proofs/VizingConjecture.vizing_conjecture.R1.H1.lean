import OMAReductions.R_VizingConjecture_vizing_conjecture_R1

/-!
# Proof of `VizingConjecture.vizing_conjecture.R1.H1`

Vizing's conjecture when `G.dominationNumber ≤ 1` or `H.dominationNumber ≤ 1`:
- If either domination number is `0`, the product is `0 ≤ (G □ H).dominationNumber`.
- If `H.dominationNumber = 1`, then `β` is nonempty and `dominationNumber_le_dominationNumber_boxProd`
  gives `G.dominationNumber ≤ (G □ H).dominationNumber`.
- If `G.dominationNumber = 1`, then `α` is nonempty and projecting a minimum dominating set of
  `G □ H` onto the second coordinate gives a dominating set of `H` of size at most
  `(G □ H).dominationNumber`.
-/

namespace OMA.P_Vizing_H1

open SimpleGraph

private lemma nonempty_of_dominationNumber_eq_one {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (h : G.dominationNumber = 1) : Nonempty α := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have h0 : G.dominationNumber = 0 :=
    Nat.le_zero.mp (dominationNumber_le_of_isDominating G ∅ (fun v => (IsEmpty.false v).elim))
  omega

private lemma dominationNumber_snd_le_boxProd {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    H.dominationNumber ≤ (G □ H).dominationNumber := by
  obtain ⟨D, hD, hcard⟩ := exists_isNDominatingSet_dominationNumber (G □ H)
  refine le_trans (dominationNumber_le_of_isDominating H (D.image Prod.snd) ?_) ?_
  · intro b
    obtain ⟨a⟩ := ‹Nonempty α›
    rcases hD (a, b) with h | ⟨⟨w, c⟩, hw, hadj⟩
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp h)))
    · rw [boxProd_adj] at hadj
      rcases hadj with ⟨-, hbc⟩ | ⟨hbc, -⟩
      · obtain rfl : b = c := hbc
        exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hw)))
      · exact Or.inr ⟨c, Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hw)),
          hbc⟩
  · rw [← hcard]
    exact Finset.card_image_le

theorem h1_proof : OMA.R_VizingConjecture_vizing_conjecture_R1.H1 := by
  intro α β _ _ _ _ G H hle
  rcases hle with hG | hH
  · have hcases : G.dominationNumber = 0 ∨ G.dominationNumber = 1 := by omega
    rcases hcases with h0 | h1
    · simp [h0]
    · haveI : Nonempty α := nonempty_of_dominationNumber_eq_one G h1
      rw [h1, one_mul]
      exact dominationNumber_snd_le_boxProd G H
  · have hcases : H.dominationNumber = 0 ∨ H.dominationNumber = 1 := by omega
    rcases hcases with h0 | h1
    · simp [h0]
    · haveI : Nonempty β := nonempty_of_dominationNumber_eq_one H h1
      rw [h1, mul_one]
      exact dominationNumber_le_dominationNumber_boxProd G H

end OMA.P_Vizing_H1

theorem OMA.solution : OMA.R_VizingConjecture_vizing_conjecture_R1.H1 :=
  OMA.P_Vizing_H1.h1_proof
