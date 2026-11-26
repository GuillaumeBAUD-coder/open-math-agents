import FormalConjectures.OpenQuantumProblems.«23»

-- Problem: Open Quantum Problem 23: SIC-POVMs — hasSICPOVM two
-- Upstream: formal-conjectures FormalConjectures/OpenQuantumProblems/23.lean:279 (declaration OpenQuantumProblem23.hasSICPOVM_two)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OpenQuantumProblem23

theorem OMA.solution : type_of% @OpenQuantumProblem23.hasSICPOVM_two := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha : tetraA ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hb : tetraB ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have ha4 : tetraA ^ 4 = 1 / 9 := by
    rw [show tetraA ^ 4 = (tetraA ^ 2) ^ 2 by ring, ha]; norm_num
  have hb4 : tetraB ^ 4 = 4 / 9 := by
    rw [show tetraB ^ 4 = (tetraB ^ 2) ^ 2 by ring, hb]; norm_num
  -- The cube root of unity and its square in Cartesian form.
  have hω : ω = ⟨-1 / 2, Real.sqrt 3 / 2⟩ := by
    apply Complex.ext <;> simp [ω]
  have hω2 : (⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
    apply Complex.ext <;> simp [pow_two] <;> nlinarith [h3]
  -- The tetrahedral states are normalized (proved upstream); check the twelve overlaps.
  refine ⟨qubitSICFamily, qubitSICFamily_normalized, ?_⟩
  intro i j hij
  have hsic : sicOverlapSq 2 = 1 / 3 := by
    simp only [sicOverlapSq]; norm_num
  rw [hsic]
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [overlapSq, qubitSICFamily, vec2, Fin.sum_univ_two, hω, hω2, Complex.normSq_apply] <;>
    ring_nf <;> simp only [ha, hb, h3, ha4, hb4] <;> ring_nf <;> nlinarith [h3, ha, hb]
