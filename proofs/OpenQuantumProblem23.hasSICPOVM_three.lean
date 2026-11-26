import FormalConjectures.OpenQuantumProblems.«23»

-- Problem: Open Quantum Problem 23: SIC-POVMs — hasSICPOVM three
-- Upstream: formal-conjectures FormalConjectures/OpenQuantumProblems/23.lean:301 (declaration OpenQuantumProblem23.hasSICPOVM_three)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OpenQuantumProblem23

theorem OMA.solution : type_of% @OpenQuantumProblem23.hasSICPOVM_three := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : hesseS ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hs4 : hesseS ^ 4 = 1 / 4 := by
    rw [show hesseS ^ 4 = (hesseS ^ 2) ^ 2 by ring, hs]; norm_num
  -- The cube root of unity and its square in Cartesian form.
  have hω : ω = ⟨-1 / 2, Real.sqrt 3 / 2⟩ := by
    apply Complex.ext <;> simp [ω]
  have hω2 : (⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
    apply Complex.ext <;> simp [pow_two] <;> nlinarith [h3]
  -- The Hesse states are normalized (proved upstream); check the 72 ordered overlaps.
  refine ⟨hesseFamily, hesseFamily_normalized, ?_⟩
  intro i j hij
  have hsic : sicOverlapSq 3 = 1 / 4 := by
    simp only [sicOverlapSq]; norm_num
  rw [hsic]
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [overlapSq, hesseFamily, vec3, Fin.sum_univ_three, hω, hω2, Complex.normSq_apply] <;>
    ring_nf <;> simp only [hs, h3, hs4] <;> ring_nf <;> nlinarith [h3, hs]
