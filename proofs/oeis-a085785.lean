import OMAStatements.S_oeis_a085785

open OMA.S_oeis_a085785

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a085785.main) := by
  intro h
  obtain ⟨m, hm⟩ := h 1 (by norm_num)
  have hc : (⌈(3 / 4 : ℚ)⌉ : ℤ) = 1 := by
    apply Int.ceil_eq_iff.mpr
    constructor <;> norm_num
  have hf : f (3 / 4 : ℚ) = 3 / 4 := by
    simp only [f, hc, Int.cast_one, mul_one]
  have hi : ∀ k : ℕ, f^[k] (3 / 4 : ℚ) = 3 / 4 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hf]
  have he : ((2 * ((1 : ℕ) : ℚ) + 1) / 4) = 3 / 4 := by norm_num
  rw [he] at hm
  rw [hi m] at hm
  norm_num at hm
