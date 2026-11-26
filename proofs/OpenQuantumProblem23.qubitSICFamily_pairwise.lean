import FormalConjectures.OpenQuantumProblems.«23»

/-!
# The tetrahedral qubit SIC has constant pairwise squared overlap

The four states are `(1,0)`, `(a,b)`, `(a,b*ω)`, `(a,b*ω^2)` with `a = sqrt(1/3)`,
`b = sqrt(2/3)` and `ω` the primitive cube root of unity.  All 16 ordered pairs are
evaluated by reducing the squared overlap to a real polynomial identity in `√2` and
`√3`, closed by the displayed power relations.
-/

open OpenQuantumProblem23

set_option maxHeartbeats 2000000 in
theorem OMA.solution : type_of% @OpenQuantumProblem23.qubitSICFamily_pairwise := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ^ 4 = 4 := by
    have e : Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
    rw [e, h2]; norm_num
  have h3' : Real.sqrt 3 ^ 4 = 9 := by
    have e : Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
    rw [e, h3]; norm_num
  have h2'' : Real.sqrt 2 ^ 8 = 16 := by
    have e : Real.sqrt 2 ^ 8 = (Real.sqrt 2 ^ 2) ^ 4 := by ring
    rw [e, h2]; norm_num
  have h3'' : Real.sqrt 3 ^ 8 = 81 := by
    have e : Real.sqrt 3 ^ 8 = (Real.sqrt 3 ^ 2) ^ 4 := by ring
    rw [e, h3]; norm_num
  have h36 : Real.sqrt 3 ^ 6 = 27 := by
    have e : Real.sqrt 3 ^ 6 = (Real.sqrt 3 ^ 2) ^ 3 := by ring
    rw [e, h3]; norm_num
  have h26 : Real.sqrt 2 ^ 6 = 8 := by
    have e : Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
    rw [e, h2]; norm_num
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try exact absurd rfl hij
  all_goals simp [overlapSq, qubitSICFamily, vec2, mkStateVector, Fin.sum_univ_two, tetraA,
    tetraB, sicOverlapSq, Complex.normSq_apply, ω, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, map_ofNat]
  all_goals (try norm_num)
  all_goals (try field_simp)
  all_goals (try ring_nf)
  all_goals (try nlinarith [h2, h3, h2', h3', h2'', h3'', h36, h26])
