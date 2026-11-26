import FormalConjectures.OpenQuantumProblems.«23»

open OpenQuantumProblem23

lemma OMA.overlap_vec2 (a b c d : ℂ) :
    overlapSq (vec2 a b) (vec2 c d) = Complex.normSq (star a * c + star b * d) := by
  simp [overlapSq, vec2, mkStateVector, Fin.sum_univ_two]

set_option maxHeartbeats 2000000 in
theorem OMA.solution : type_of% @OpenQuantumProblem23.qubitSICFamily_pairwise := by
  have ha : tetraA ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hb : tetraB ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha4 : tetraA ^ 4 = (1 / 3 : ℝ) ^ 2 := by rw [← ha]; ring
  have hb4 : tetraB ^ 4 = (2 / 3 : ℝ) ^ 2 := by rw [← hb]; ring
  have hs4 : Real.sqrt 3 ^ 4 = 9 := by nlinarith only [congrArg (fun t : ℝ => t ^ 2) hs]
  have hs6 : Real.sqrt 3 ^ 6 = 27 := by rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, hs]; norm_num
  have hs8 : Real.sqrt 3 ^ 8 = 81 := by rw [show (8 : ℕ) = 2 * 4 by decide, pow_mul, hs]; norm_num
  intro i j hij
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals
    norm_num [qubitSICFamily, OMA.overlap_vec2, sicOverlapSq, ω, Complex.normSq_apply,
      Complex.star_def, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two]
  all_goals
    ring_nf
  all_goals
    norm_num [ha, hb, hs, ha4, hb4, hs4, hs6, hs8] <;> ring
