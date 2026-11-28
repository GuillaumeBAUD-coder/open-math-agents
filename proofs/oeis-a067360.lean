import OMAStatements.S_oeis_a067360

namespace OMA.P067360

open OMA.S_oeis_a067360 Real

noncomputable def th : ℝ := 2 * arctan (1 / 4)

noncomputable def c (n : ℕ) : ℝ := 17 ^ n * cos ((n : ℝ) * th)

lemma a_eq (n : ℕ) : a n = 17 ^ n * sin ((n : ℝ) * th) := by
  unfold a th
  congr 2
  ring

lemma cos_sq : cos (arctan (1 / 4)) ^ 2 = 16 / 17 := by
  rw [cos_sq_arctan]
  norm_num

lemma cos_th : cos th = 15 / 17 := by
  unfold th
  rw [cos_two_mul, cos_sq]
  norm_num

lemma sin_th : sin th = 8 / 17 := by
  unfold th
  have hne : cos (arctan (1 / 4)) ≠ 0 := (cos_arctan_pos _).ne'
  have ht : sin (arctan (1 / 4)) = (1 / 4) * cos (arctan (1 / 4)) := by
    rw [← tan_arctan (1 / 4 : ℝ)]
    rw [arctan_tan] <;> first | exact (tan_mul_cos hne).symm | skip
    all_goals first | exact neg_pi_div_two_lt_arctan _ | exact arctan_lt_pi_div_two _
  rw [sin_two_mul, ht]
  have := cos_sq
  nlinarith

lemma step (n : ℕ) : a (n + 1) = 15 * a n + 8 * c n ∧ c (n + 1) = 15 * c n - 8 * a n := by
  have e : ((n + 1 : ℕ) : ℝ) * th = (n : ℝ) * th + th := by push_cast; ring
  rw [a_eq, a_eq]
  unfold c
  rw [e, sin_add, cos_add, cos_th, sin_th, pow_succ]
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
