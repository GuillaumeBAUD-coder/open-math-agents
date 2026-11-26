import FormalConjectures.WrittenOnTheWallII.Test

-- Problem: Testing Graph Invariants — C6 girth
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/Test.lean:422 (declaration WrittenOnTheWallII.Test.C6_girth)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open SimpleGraph

namespace OMA

lemma C6_no_triangle : ∀ a b c : Fin 6, (cycleGraph 6).Adj a b → (cycleGraph 6).Adj b c →
    (cycleGraph 6).Adj c a → False := by decide

lemma C6_no_square : ∀ a b c d : Fin 6, (cycleGraph 6).Adj a b → (cycleGraph 6).Adj b c →
    (cycleGraph 6).Adj c d → (cycleGraph 6).Adj d a → a ≠ c → b ≠ d → False := by decide

set_option maxRecDepth 100000 in
lemma C6_no_pentagon : ∀ a b c d e : Fin 6, (cycleGraph 6).Adj a b → (cycleGraph 6).Adj b c →
    (cycleGraph 6).Adj c d → (cycleGraph 6).Adj d e → (cycleGraph 6).Adj e a → False := by
  decide +kernel

end OMA

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.C6_girth := by
  show (cycleGraph 6).girth = 6
  have hcyc : (Walk.cons (show (cycleGraph 6).Adj 0 1 by decide)
      (Walk.cons (show (cycleGraph 6).Adj 1 2 by decide)
      (Walk.cons (show (cycleGraph 6).Adj 2 3 by decide)
      (Walk.cons (show (cycleGraph 6).Adj 3 4 by decide)
      (Walk.cons (show (cycleGraph 6).Adj 4 5 by decide)
      (Walk.cons (show (cycleGraph 6).Adj 5 0 by decide) Walk.nil)))))).IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  refine le_antisymm (by simpa using girth_le_length hcyc) ?_
  obtain ⟨a, c, hc, hlen⟩ := exists_girth_eq_length.2 (fun hac => hac _ hcyc)
  rw [hlen]
  by_contra hlt
  rw [not_le] at hlt
  have h3 := hc.three_le_length
  have A : ∀ i < c.length, (cycleGraph 6).Adj (c.getVert i) (c.getVert (i + 1)) :=
    fun i hi => c.adj_getVert_succ hi
  have e0 : c.getVert 0 = a := c.getVert_zero
  have eL : c.getVert c.length = a := c.getVert_length
  have inj := hc.getVert_injOn'
  have h0 := A 0 (by omega)
  rw [e0] at h0
  interval_cases hL : c.length
  · have h2 := A 2 (by norm_num)
    rw [eL] at h2
    exact OMA.C6_no_triangle _ _ _ h0 (A 1 (by norm_num)) h2
  · have h3' := A 3 (by norm_num)
    rw [eL] at h3'
    refine OMA.C6_no_square _ _ _ _ h0 (A 1 (by norm_num)) (A 2 (by norm_num))
      h3' (fun h => ?_) (fun h => ?_)
    · have := inj (x₁ := 0) (x₂ := 2) (by simp) (by simp) (e0.trans h)
      omega
    · have := inj (x₁ := 1) (x₂ := 3) (by simp) (by simp) h
      omega
  · have h4 := A 4 (by norm_num)
    rw [eL] at h4
    exact OMA.C6_no_pentagon _ _ _ _ _ h0 (A 1 (by norm_num))
      (A 2 (by norm_num)) (A 3 (by norm_num)) h4
