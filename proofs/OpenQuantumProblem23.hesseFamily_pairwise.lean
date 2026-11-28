import FormalConjectures.OpenQuantumProblems.«23»

/-! Pairwise squared overlaps of the nine Hesse qutrit states. -/

open OpenQuantumProblem23

private def E : Fin 9 → Fin 3 → ℤ × ℤ :=
  ![![(0,0),(2,0),(-2,0)], ![(0,0),(2,0),(1,-1)], ![(0,0),(2,0),(1,1)],
    ![(-2,0),(0,0),(2,0)], ![(1,-1),(0,0),(2,0)], ![(1,1),(0,0),(2,0)],
    ![(2,0),(-2,0),(0,0)], ![(2,0),(1,-1),(0,0)], ![(2,0),(1,1),(0,0)]]

private def dR (u v : Fin 3 → ℤ × ℤ) : ℤ := ∑ k, ((u k).1 * (v k).1 + 3 * (u k).2 * (v k).2)
private def dI (u v : Fin 3 → ℤ × ℤ) : ℤ := ∑ k, ((u k).1 * (v k).2 - (u k).2 * (v k).1)

theorem OMA.solution : type_of% @OpenQuantumProblem23.hesseFamily_pairwise := by
  intro i j hij
  let c (z : ℤ × ℤ) : ℂ := ⟨(hesseS / 2) * z.1, (hesseS / 2) * Real.sqrt 3 * z.2⟩
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcoord (a : Fin 9) (k : Fin 3) : hesseFamily a k = c (E a k) := by
    have h0 : (0 : ℂ) = c (0,0) := by apply Complex.ext <;> simp [c]
    have h1 : (hesseS : ℂ) = c (2,0) := by apply Complex.ext <;> simp [c]
    have h2 : -(hesseS : ℂ) = c (-2,0) := by apply Complex.ext <;> simp [c]
    have h3 : -((hesseS : ℂ) * ω) = c (1,-1) := by
      apply Complex.ext <;> norm_num [c, ω, Complex.mul_re, Complex.mul_im] <;> ring
    have h4 : -((hesseS : ℂ) * ω ^ 2) = c (1,1) := by
      apply Complex.ext <;> norm_num [c, ω, pow_two, Complex.mul_re, Complex.mul_im]
      · ring_nf; rw [hr]; ring
      · ring
    fin_cases a <;> fin_cases k <;> first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
  have hdot (u v : Fin 3 → ℤ × ℤ) : (∑ k, star (c (u k)) * c (v k)) =
      (⟨(hesseS / 2) ^ 2 * dR u v, (hesseS / 2) ^ 2 * Real.sqrt 3 * dI u v⟩ : ℂ) := by
    apply Complex.ext
    · simp only [Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
        c, dR, Int.cast_sum, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring_nf; rw [hr]; ring
    · simp only [Complex.im_sum, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        c, dI, Int.cast_sum, Int.cast_sub, Int.cast_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ a b : Fin 9, a ≠ b → dR (E a) (E b) ^ 2 + 3 * dI (E a) (E b) ^ 2 = 16 := by decide +kernel
  have hnum : (dR (E i) (E j) : ℝ) ^ 2 + 3 * (dI (E i) (E j) : ℝ) ^ 2 = 16 := by exact_mod_cast hint i j hij
  have hs : hesseS ^ 2 = (1 / 2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs4 : (hesseS / 2) ^ 4 = (1 / 64 : ℝ) := by rw [div_pow, show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs]; norm_num
  simp only [overlapSq, hcoord, hdot, Complex.normSq_apply, sicOverlapSq]
  calc _ = (hesseS / 2) ^ 4 * ((dR (E i) (E j) : ℝ) ^ 2 + Real.sqrt 3 ^ 2 * (dI (E i) (E j) : ℝ) ^ 2) := by ring
    _ = _ := by rw [hr, hnum, hs4]; norm_num
