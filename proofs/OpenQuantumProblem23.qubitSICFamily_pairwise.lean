import FormalConjectures.OpenQuantumProblems.«23»

-- Problem: Open Quantum Problem 23: SIC-POVMs — qubitSICFamily pairwise
-- Upstream: formal-conjectures FormalConjectures/OpenQuantumProblems/23.lean:274 (declaration OpenQuantumProblem23.qubitSICFamily_pairwise)
-- Credit: @iskan-ai (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OpenQuantumProblem23

namespace OMA.QubitSIC

lemma tA2 : tetraA ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
lemma tB2 : tetraB ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
lemma tA4 : tetraA ^ 4 = 1 / 9 := by rw [show 4 = 2 * 2 from rfl, pow_mul, tA2]; norm_num
lemma tB4 : tetraB ^ 4 = 4 / 9 := by rw [show 4 = 2 * 2 from rfl, pow_mul, tB2]; norm_num
lemma s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma s34 : Real.sqrt 3 ^ 4 = 9 := by rw [show 4 = 2 * 2 from rfl, pow_mul, s3]; norm_num
lemma ω_re : ω.re = -1 / 2 := by simp [ω]
lemma ω_im : ω.im = Real.sqrt 3 / 2 := by simp [ω]
lemma ω2_re : (ω ^ 2).re = -1 / 2 := by
  rw [pow_two, Complex.mul_re, ω_re, ω_im]; nlinarith [s3]
lemma ω2_im : (ω ^ 2).im = -(Real.sqrt 3 / 2) := by
  rw [pow_two, Complex.mul_im, ω_re, ω_im]; ring
lemma cω2_re : ((starRingEnd ℂ) ω ^ 2).re = -1 / 2 := by
  rw [← map_pow, Complex.conj_re, ω2_re]
lemma cω2_im : ((starRingEnd ℂ) ω ^ 2).im = Real.sqrt 3 / 2 := by
  rw [← map_pow, Complex.conj_im, ω2_im]; ring

end OMA.QubitSIC

open OMA.QubitSIC in
theorem OMA.solution : type_of% @OpenQuantumProblem23.qubitSICFamily_pairwise := by
  intro i j hij
  rw [sicOverlapSq_two]
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [overlapSq, qubitSICFamily, vec2, Fin.sum_univ_two, Complex.normSq_apply,
      ω_re, ω_im, ω2_re, ω2_im, cω2_re, cω2_im] <;>
    ring_nf <;> simp [tA2, tB2, tA4, tB4, s34] <;> norm_num
