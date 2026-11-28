import OMAStatements.S_wp_representation

-- Problem: Graphs needing more than ⌊n/2⌋ copies of each letter in a word-representant
-- Upstream: formal-conjectures statements/wp-representation.lean:0 (declaration OMA.S_wp_representation.main)
-- Credit: @LordDavidDev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_wp_representation

theorem OMA.solution : type_of% @OMA.S_wp_representation.main := by
  -- Witness: the empty graph on two vertices.  Any word in which each of the two letters occurs
  -- exactly once is [0, 1] or [1, 0], and those alternate, so it represents the complete graph,
  -- not the empty one.  Two copies of each letter do represent the empty graph.
  refine ⟨2, ⊥, ⟨2, by norm_num, [0, 1, 1, 0], by decide, ?_⟩, ?_⟩
  · intro x y hxy
    have h01 : ¬ Alternate ([0, 1, 1, 0] : List (Fin 2)) 0 1 := by
      show ¬ List.IsChain (fun a b : Fin 2 => a ≠ b)
        ([0, 1, 1, 0].filter fun z => decide (z = 0 ∨ z = 1))
      decide
    have h10 : ¬ Alternate ([0, 1, 1, 0] : List (Fin 2)) 1 0 := by
      show ¬ List.IsChain (fun a b : Fin 2 => a ≠ b)
        ([0, 1, 1, 0].filter fun z => decide (z = 1 ∨ z = 0))
      decide
    have hxy' : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
      revert hxy
      fin_cases x <;> fin_cases y <;> simp
    rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using h01
    · simpa using h10
  intro k hk w hw
  have hk1 : k ≤ 1 := by simpa using hk
  have hsplit : k = 0 ∨ k = 1 := by omega
  rcases hsplit with rfl | rfl
  · -- k = 0: a word with no letters at all is empty, and the empty word alternates.
    have h0 : w.count (0 : Fin 2) = 0 := hw.1 0
    have h1 : w.count (1 : Fin 2) = 0 := hw.1 1
    have hnil : w = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro z hz
      rcases (show z = 0 ∨ z = 1 by fin_cases z <;> simp) with hz0 | hz1
      · exact (List.count_eq_zero.mp (hz0 ▸ h0)) hz
      · exact (List.count_eq_zero.mp (hz1 ▸ h1)) hz
    have hlink := hw.2 0 1 (by decide)
    rw [hnil] at hlink
    exact (by simp : ¬ (⊥ : SimpleGraph (Fin 2)).Adj 0 1)
      (hlink.mpr (by
        show List.IsChain (fun a b : Fin 2 => a ≠ b)
          (([] : List (Fin 2)).filter fun z => decide (z = 0 ∨ z = 1))
        exact List.IsChain.nil))
  · -- k = 1: each letter occurs once, so w is [0, 1] or [1, 0], which alternates.
    have h0 : w.count (0 : Fin 2) = 1 := hw.1 0
    have h1 : w.count (1 : Fin 2) = 1 := hw.1 1
    have hnd : w.Nodup := by
      rw [List.nodup_iff_count_le_one]
      intro a
      rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with ha | ha
      · exact ha ▸ le_of_eq h0
      · exact ha ▸ le_of_eq h1
    have hchain : w.IsChain (fun a b => a ≠ b) := List.Pairwise.isChain hnd
    have hfilt : w.filter (fun z => decide (z = 0 ∨ z = 1)) = w := by
      rw [List.filter_eq_self]
      intro a _
      rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with ha | ha <;> simp [ha]
    have hlink := hw.2 0 1 (by decide)
    have halt : Alternate w 0 1 := by
      show List.IsChain (fun a b => a ≠ b) (w.filter fun z => decide (z = 0 ∨ z = 1))
      rw [hfilt]
      exact hchain
    exact (by simp : ¬ (⊥ : SimpleGraph (Fin 2)).Adj 0 1) (hlink.mpr halt)
