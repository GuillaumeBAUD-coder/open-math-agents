import OMAStatements.S_oeis_a067360

namespace OMA.P067360

open OMA.S_oeis_a067360

noncomputable def th : ℝ := 2 * Real.arctan (1 / 4)

noncomputable def c (n : ℕ) : ℝ := 17 ^ n * Real.cos ((n : ℝ) * th)

lemma a_eq (n : ℕ) : a n = 17 ^ n * Real.sin ((n : ℝ) * th) := by
  unfold a th
  congr 2
  ring

lemma cos_sq : Real.cos (Real.arctan (1 / 4)) ^ 2 = 16 / 17 := by
  rw [Real.cos_sq_arctan]
  norm_num

lemma cos_th : Real.cos th = 15 / 17 := by
  unfold th
  rw [Real.cos_two_mul, cos_sq]
  norm_num

lemma sin_th : Real.sin th = 8 / 17 := by
  unfold th
  have hne : Real.cos (Real.arctan (1 / 4)) ≠ 0 := (Real.cos_arctan_pos _).ne'
  have ht : Real.sin (Real.arctan (1 / 4)) = (1 / 4) * Real.cos (Real.arctan (1 / 4)) := by
    rw [← Real.tan_arctan (1 / 4 : ℝ)]
    rw [Real.arctan_tan] <;> first | exact (Real.tan_mul_cos hne).symm | skip
    all_goals first | exact Real.neg_pi_div_two_lt_arctan _ | exact Real.arctan_lt_pi_div_two _
  rw [Real.sin_two_mul, ht]
  have := cos_sq
  nlinarith

lemma step (n : ℕ) : a (n + 1) = 15 * a n + 8 * c n ∧ c (n + 1) = 15 * c n - 8 * a n := by
  have e : ((n + 1 : ℕ) : ℝ) * th = (n : ℝ) * th + th := by push_cast; ring
  rw [a_eq, a_eq]
  unfold c
  rw [e, Real.sin_add, Real.cos_add, cos_th, sin_th, pow_succ]
  constructor <;> ring

lemma pow_plus (n : ℕ) :
    (15 + 8 * Complex.I) ^ n = (c n : ℂ) + (a n : ℂ) * Complex.I := by
  induction n with
  | zero => simp [c, a]
  | succ n ih =>
    rw [pow_succ, ih, (step n).1, (step n).2]
    push_cast
    linear_combination (8 * (a n : ℂ)) * Complex.I_sq

lemma pow_minus (n : ℕ) :
    (15 - 8 * Complex.I) ^ n = (c n : ℂ) - (a n : ℂ) * Complex.I := by
  induction n with
  | zero => simp [c, a]
  | succ n ih =>
    rw [pow_succ, ih, (step n).1, (step n).2]
    push_cast
    linear_combination (8 * (a n : ℂ)) * Complex.I_sq

end OMA.P067360

open OMA.S_oeis_a067360 OMA.P067360 in
theorem OMA.solution : type_of% @OMA.S_oeis_a067360.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have e1 : m + 2 - 1 = m + 1 := by omega
    have e2 : m + 2 - 2 = m := by omega
    rw [e1, e2]
    have h1 := step m
    have h2 := step (m + 1)
    linarith [h1.1, h1.2, h2.1, h2.2]
  · intro n _
    rw [pow_plus, pow_minus]
    linear_combination (a n : ℂ) * Complex.I_sq
