import FormalConjectures.OpenQuantumProblems.«23»

-- Problem: Open Quantum Problem 23: SIC-POVMs — qubitSICFamily pairwise
-- Upstream: formal-conjectures FormalConjectures/OpenQuantumProblems/23.lean:274 (declaration OpenQuantumProblem23.qubitSICFamily_pairwise)
-- Credit: @Ronandt (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OpenQuantumProblem23

namespace OMA.QubitSICPairwise

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma overlapSq_vec2 (a₁ b₁ a₂ b₂ : ℂ) :
    overlapSq (vec2 a₁ b₁) (vec2 a₂ b₂) =
      Complex.normSq (star a₁ * a₂ + star b₁ * b₂) := by
  simp [overlapSq, vec2, Fin.sum_univ_two]

lemma normSq_tetraA : Complex.normSq (tetraA : ℂ) = 1 / 3 := by
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
  exact Real.mul_self_sqrt (by norm_num)

lemma normSq_star_tetraA : Complex.normSq (star (tetraA : ℂ)) = 1 / 3 := by
  simp only [Complex.normSq_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, mul_zero, add_zero]
  exact Real.mul_self_sqrt (by norm_num)

lemma normSq_pair (z : ℂ) (hre : z.re = -1 / 2) (him : z.im ^ 2 = 3 / 4) :
    Complex.normSq
      (star (tetraA : ℂ) * (tetraA : ℂ) +
        star (tetraB : ℂ) * (tetraB : ℂ) * z) = 1 / 3 := by
  have ha : tetraA * tetraA = 1 / 3 := Real.mul_self_sqrt (by norm_num)
  have hb : tetraB * tetraB = 2 / 3 := Real.mul_self_sqrt (by norm_num)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, hre]
  calc
    _ = (tetraA * tetraA - (tetraB * tetraB) / 2) ^ 2 +
          (tetraB * tetraB) ^ 2 * z.im ^ 2 := by ring
    _ = 1 / 3 := by rw [ha, hb, him]; norm_num

lemma omega_re : ω.re = -1 / 2 := by
  simp [ω]

lemma omega_im : ω.im = Real.sqrt 3 / 2 := by
  simp [ω]

lemma omega_sq_re : (ω ^ 2).re = -1 / 2 := by
  simp only [pow_two, Complex.mul_re, omega_re, omega_im]
  calc
    _ = 1 / 4 - Real.sqrt 3 ^ 2 / 4 := by ring
    _ = -1 / 2 := by rw [sqrt3_sq]; norm_num

lemma omega_sq_im : (ω ^ 2).im = -(Real.sqrt 3 / 2) := by
  simp only [pow_two, Complex.mul_im, omega_re, omega_im]
  ring

lemma omega_im_sq : ω.im ^ 2 = 3 / 4 := by
  rw [omega_im]
  calc
    _ = Real.sqrt 3 ^ 2 / 4 := by ring
    _ = 3 / 4 := by rw [sqrt3_sq]

lemma omega_sq_im_sq : (ω ^ 2).im ^ 2 = 3 / 4 := by
  rw [omega_sq_im]
  calc
    _ = Real.sqrt 3 ^ 2 / 4 := by ring
    _ = 3 / 4 := by rw [sqrt3_sq]

lemma star_omega_mul_sq_re : (star ω * ω ^ 2).re = -1 / 2 := by
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    omega_re, omega_im, omega_sq_re, omega_sq_im]
  calc
    _ = 1 / 4 - Real.sqrt 3 ^ 2 / 4 := by ring
    _ = -1 / 2 := by rw [sqrt3_sq]; norm_num

lemma star_omega_mul_sq_im_sq : (star ω * ω ^ 2).im ^ 2 = 3 / 4 := by
  simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    omega_re, omega_im, omega_sq_re, omega_sq_im]
  calc
    _ = Real.sqrt 3 ^ 2 / 4 := by ring
    _ = 3 / 4 := by rw [sqrt3_sq]

lemma star_omega_sq_mul_re : (star (ω ^ 2) * ω).re = -1 / 2 := by
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    omega_re, omega_im, omega_sq_re, omega_sq_im]
  calc
    _ = 1 / 4 - Real.sqrt 3 ^ 2 / 4 := by ring
    _ = -1 / 2 := by rw [sqrt3_sq]; norm_num

lemma star_omega_sq_mul_im_sq : (star (ω ^ 2) * ω).im ^ 2 = 3 / 4 := by
  simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    omega_re, omega_im, omega_sq_re, omega_sq_im]
  calc
    _ = Real.sqrt 3 ^ 2 / 4 := by ring
    _ = 3 / 4 := by rw [sqrt3_sq]

end OMA.QubitSICPairwise

open OMA.QubitSICPairwise

theorem OMA.solution : type_of% @OpenQuantumProblem23.qubitSICFamily_pairwise := by
  intro i j hij
  rw [sicOverlapSq_two]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · change overlapSq (vec2 1 0) (vec2 (tetraA : ℂ) (tetraB : ℂ)) = 1 / 3
    rw [overlapSq_vec2]
    simp only [star_one, one_mul, star_zero, zero_mul, add_zero]
    exact normSq_tetraA
  · change overlapSq (vec2 1 0) (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω)) = 1 / 3
    rw [overlapSq_vec2]
    simp only [star_one, one_mul, star_zero, zero_mul, add_zero]
    exact normSq_tetraA
  · change overlapSq (vec2 1 0) (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω ^ 2)) = 1 / 3
    rw [overlapSq_vec2]
    simp only [star_one, one_mul, star_zero, zero_mul, add_zero]
    exact normSq_tetraA
  · change overlapSq (vec2 (tetraA : ℂ) (tetraB : ℂ)) (vec2 1 0) = 1 / 3
    rw [overlapSq_vec2]
    simp only [mul_one, mul_zero, add_zero]
    exact normSq_star_tetraA
  · exact absurd rfl hij
  · change overlapSq (vec2 (tetraA : ℂ) (tetraB : ℂ))
      (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω)) = 1 / 3
    rw [overlapSq_vec2, ← mul_assoc]
    exact normSq_pair ω omega_re omega_im_sq
  · change overlapSq (vec2 (tetraA : ℂ) (tetraB : ℂ))
      (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω ^ 2)) = 1 / 3
    rw [overlapSq_vec2, ← mul_assoc]
    exact normSq_pair (ω ^ 2) omega_sq_re omega_sq_im_sq
  · change overlapSq (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω)) (vec2 1 0) = 1 / 3
    rw [overlapSq_vec2]
    simp only [mul_one, mul_zero, add_zero]
    exact normSq_star_tetraA
  · change overlapSq (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω))
      (vec2 (tetraA : ℂ) (tetraB : ℂ)) = 1 / 3
    rw [overlapSq_vec2]
    rw [show star ((tetraB : ℂ) * ω) * (tetraB : ℂ) =
        star (tetraB : ℂ) * (tetraB : ℂ) * star ω by rw [star_mul]; ring]
    exact normSq_pair (star ω)
      (by simp only [Complex.star_def, Complex.conj_re, omega_re])
      (by simp only [Complex.star_def, Complex.conj_im, neg_sq, omega_im_sq])
  · exact absurd rfl hij
  · change overlapSq (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω))
      (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω ^ 2)) = 1 / 3
    rw [overlapSq_vec2]
    rw [show star ((tetraB : ℂ) * ω) * ((tetraB : ℂ) * ω ^ 2) =
        star (tetraB : ℂ) * (tetraB : ℂ) * (star ω * ω ^ 2) by rw [star_mul]; ring]
    exact normSq_pair (star ω * ω ^ 2) star_omega_mul_sq_re star_omega_mul_sq_im_sq
  · change overlapSq (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω ^ 2)) (vec2 1 0) = 1 / 3
    rw [overlapSq_vec2]
    simp only [mul_one, mul_zero, add_zero]
    exact normSq_star_tetraA
  · change overlapSq (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω ^ 2))
      (vec2 (tetraA : ℂ) (tetraB : ℂ)) = 1 / 3
    rw [overlapSq_vec2]
    rw [show star ((tetraB : ℂ) * ω ^ 2) * (tetraB : ℂ) =
        star (tetraB : ℂ) * (tetraB : ℂ) * star (ω ^ 2) by rw [star_mul]; ring]
    exact normSq_pair (star (ω ^ 2))
      (by simp only [Complex.star_def, Complex.conj_re, omega_sq_re])
      (by simp only [Complex.star_def, Complex.conj_im, neg_sq, omega_sq_im_sq])
  · change overlapSq (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω ^ 2))
      (vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω)) = 1 / 3
    rw [overlapSq_vec2]
    rw [show star ((tetraB : ℂ) * ω ^ 2) * ((tetraB : ℂ) * ω) =
        star (tetraB : ℂ) * (tetraB : ℂ) * (star (ω ^ 2) * ω) by rw [star_mul]; ring]
    exact normSq_pair (star (ω ^ 2) * ω) star_omega_sq_mul_re star_omega_sq_mul_im_sq
  · exact absurd rfl hij
