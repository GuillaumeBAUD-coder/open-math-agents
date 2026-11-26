import FormalConjectures.OpenQuantumProblems.«23»

/-! Pairwise squared overlaps of the nine Hesse qutrit states. -/

open OpenQuantumProblem23

namespace OMA.Hesse

-- A pair (a,b) represents (s/2)(a + b i√3), where s = √(1/2).
noncomputable def coord (z : ℤ × ℤ) : ℂ :=
  ⟨(hesseS / 2) * z.1, (hesseS / 2) * Real.sqrt 3 * z.2⟩

def entries : Fin 9 → Fin 3 → ℤ × ℤ
  | 0 => ![(0,0), (2,0), (-2,0)]
  | 1 => ![(0,0), (2,0), (1,-1)]
  | 2 => ![(0,0), (2,0), (1,1)]
  | 3 => ![(-2,0), (0,0), (2,0)]
  | 4 => ![(1,-1), (0,0), (2,0)]
  | 5 => ![(1,1), (0,0), (2,0)]
  | 6 => ![(2,0), (-2,0), (0,0)]
  | 7 => ![(2,0), (1,-1), (0,0)]
  | _ => ![(2,0), (1,1), (0,0)]

lemma coordinates (i : Fin 9) (k : Fin 3) : hesseFamily i k = coord (entries i k) := by
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hz : (0 : ℂ) = coord (0,0) := by apply Complex.ext <;> simp [coord]
  have hu : (hesseS : ℂ) = coord (2,0) := by apply Complex.ext <;> simp [coord]
  have hv : -(hesseS : ℂ) = coord (-2,0) := by apply Complex.ext <;> simp [coord]
  have hw : -((hesseS : ℂ) * ω) = coord (1,-1) := by
    apply Complex.ext <;> norm_num [coord, ω, Complex.mul_re, Complex.mul_im] <;> ring
  have hw2 : -((hesseS : ℂ) * ω ^ 2) = coord (1,1) := by
    apply Complex.ext <;> norm_num [coord, ω, pow_two, Complex.mul_re, Complex.mul_im]
    all_goals ring_nf
    all_goals norm_num [hr]
    all_goals ring
  fin_cases i <;> fin_cases k <;> first | exact hz | exact hu | exact hv | exact hw | exact hw2

def dotRe (u v : Fin 3 → ℤ × ℤ) : ℤ :=
  ∑ k, ((u k).1 * (v k).1 + 3 * (u k).2 * (v k).2)

def dotIm (u v : Fin 3 → ℤ × ℤ) : ℤ :=
  ∑ k, ((u k).1 * (v k).2 - (u k).2 * (v k).1)

lemma dot_formula (u v : Fin 3 → ℤ × ℤ) :
    (∑ k, star (coord (u k)) * coord (v k)) =
      (⟨(hesseS / 2) ^ 2 * dotRe u v,
        (hesseS / 2) ^ 2 * Real.sqrt 3 * dotIm u v⟩ : ℂ) := by
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, coord, dotRe, Int.cast_sum, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring_nf
    rw [hr]
    ring
  · simp only [Complex.im_sum, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, coord, dotIm, Int.cast_sum, Int.cast_sub, Int.cast_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

-- After removing the common scale, each distinct pair has squared norm 16.
lemma integer_overlaps : ∀ i j : Fin 9, i ≠ j →
    dotRe (entries i) (entries j) ^ 2 + 3 * dotIm (entries i) (entries j) ^ 2 = 16 := by
  decide +kernel

end OMA.Hesse

open OMA.Hesse

theorem OMA.solution : type_of% @OpenQuantumProblem23.hesseFamily_pairwise := by
  intro i j hij
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : hesseS ^ 2 = (1 / 2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs4 : (hesseS / 2) ^ 4 = (1 / 64 : ℝ) := by
    rw [div_pow, show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs]
    norm_num
  have hnum : (dotRe (entries i) (entries j) : ℝ) ^ 2 +
      3 * (dotIm (entries i) (entries j) : ℝ) ^ 2 = 16 := by
    exact_mod_cast integer_overlaps i j hij
  simp only [overlapSq, coordinates, dot_formula, Complex.normSq_apply, sicOverlapSq]
  calc
    _ = (hesseS / 2) ^ 4 * ((dotRe (entries i) (entries j) : ℝ) ^ 2 +
          Real.sqrt 3 ^ 2 * (dotIm (entries i) (entries j) : ℝ) ^ 2) := by ring
    _ = _ := by rw [hr, hnum, hs4]; norm_num
