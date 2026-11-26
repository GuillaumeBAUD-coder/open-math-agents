import FormalConjectures.WrittenOnTheWallII.Test

-- Problem: Testing Graph Invariants — petersen girth
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/Test.lean:315 (declaration WrittenOnTheWallII.Test.petersen_girth)
-- Credit: @ashnewmanjones (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open SimpleGraph

lemma OMA.petersen_no_triangle (a b c : PetersenVertex) :
    petersenGraph.Adj a b → petersenGraph.Adj b c → ¬ petersenGraph.Adj c a := by
  revert a b c; decide +kernel

lemma OMA.petersen_no_square (a b c d : PetersenVertex) :
    petersenGraph.Adj a b → petersenGraph.Adj b c → petersenGraph.Adj c d →
      petersenGraph.Adj d a → b ≠ d → a = c := by
  have key : ∀ a b c d : PetersenVertex, petersenGraph.Adj a b → petersenGraph.Adj b c →
      petersenGraph.Adj c d → petersenGraph.Adj d a → b.1 = d.1 ∨ a.1 = c.1 := by
    decide +kernel
  intro h1 h2 h3 h4 hbd
  rcases key a b c d h1 h2 h3 h4 with h | h
  · exact absurd (Subtype.ext h) hbd
  · exact Subtype.ext h

lemma OMA.petersen_five_le_length {a : PetersenVertex} (w : petersenGraph.Walk a a)
    (hw : w.IsCycle) : 5 ≤ w.length := by
  have h3 := hw.three_le_length
  by_contra hlt
  rw [not_le] at hlt
  rcases w with _ | ⟨h1, w⟩
  · simp at h3
  rcases w with _ | ⟨h2, w⟩
  · simp at h3
  rcases w with _ | ⟨h3', w⟩
  · simp at h3
  rcases w with _ | ⟨h4, w⟩
  · exact OMA.petersen_no_triangle _ _ _ h1 h2 h3'
  rcases w with _ | ⟨h5, w⟩
  · have hnd := hw.support_nodup
    simp [Walk.support_cons] at hnd
    have hac := OMA.petersen_no_square _ _ _ _ h1 h2 h3' h4 (by tauto)
    subst hac
    simp at hnd
  · simp at hlt
    omega

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.petersen_girth := by
  have hcyc : (Walk.cons
      (show petersenGraph.Adj (⟨{0, 1}, by decide⟩ : PetersenVertex) ⟨{2, 3}, by decide⟩ by decide)
      (Walk.cons
      (show petersenGraph.Adj (⟨{2, 3}, by decide⟩ : PetersenVertex) ⟨{0, 4}, by decide⟩ by decide)
      (Walk.cons
      (show petersenGraph.Adj (⟨{0, 4}, by decide⟩ : PetersenVertex) ⟨{1, 2}, by decide⟩ by decide)
      (Walk.cons
      (show petersenGraph.Adj (⟨{1, 2}, by decide⟩ : PetersenVertex) ⟨{3, 4}, by decide⟩ by decide)
      (Walk.cons
      (show petersenGraph.Adj (⟨{3, 4}, by decide⟩ : PetersenVertex) ⟨{0, 1}, by decide⟩ by decide)
      Walk.nil))))).IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  have hle : petersenGraph.egirth ≤ 5 := by
    simpa using egirth_le_length hcyc
  have hge : (5 : ℕ∞) ≤ petersenGraph.egirth := by
    rw [le_egirth]
    intro a w hw
    exact_mod_cast OMA.petersen_five_le_length w hw
  have heq : petersenGraph.egirth = 5 := le_antisymm hle hge
  show petersenGraph.girth = 5
  rw [girth, heq]
  rfl
