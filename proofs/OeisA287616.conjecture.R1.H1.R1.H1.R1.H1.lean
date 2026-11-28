import OMAReductions.R_OeisA287616_conjecture_R1_H1_R1_H1_R1

-- Step H1 of reduction OeisA287616.conjecture.R1.H1.R1.H1.R1: local solvability at p = 2, 3, 5 via Hensel's lemma.
-- Credit: @GiridhariPradeep (agent: Claude Code, model claude-opus-5-5)

open Polynomial

namespace OMA.A287

lemma sqrt_exists {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) (hx : ‖x - 1‖ < ‖(2 : ℤ_[p])‖ ^ 2) :
    ∃ z : ℤ_[p], z ^ 2 = x := by
  have hnorm : ‖(X ^ 2 - C x : Polynomial ℤ_[p]).aeval (1 : ℤ_[p])‖ <
      ‖(X ^ 2 - C x : Polynomial ℤ_[p]).derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, one_pow, derivative_X_pow,
      derivative_C, sub_zero, map_mul, map_natCast, Algebra.algebraMap_self, RingHom.id_apply]
    rw [norm_sub_rev]
    simpa using hx
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  simp only [map_sub, map_pow, aeval_X, aeval_C, Algebra.algebraMap_self, RingHom.id_apply] at hz
  exact sub_eq_zero.mp hz

lemma norm_mul_le_of {p : ℕ} [Fact p.Prime] (k : ℤ_[p]) (y : ℤ_[p]) : ‖k * y‖ ≤ ‖k‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one y)

theorem h1 : ∀ (n p : ℕ) [Fact p.Prime], p ∣ 30 →
    ∃ a b c : ℤ_[p],
      15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 120 * (n : ℤ_[p]) + 23 ∧
        (IsUnit a ∨ IsUnit b ∨ IsUnit c) := by
  intro n p hp h30
  have hpp := (Fact.out : p.Prime)
  have hp' : p = 2 ∨ p = 3 ∨ p = 5 := by
    have hle : p ≤ 30 := Nat.le_of_dvd (by norm_num) h30
    interval_cases p <;> first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | (revert hpp h30; norm_num)
  rcases hp' with rfl | rfl | rfl
  · -- p = 2 : a = b = 1, c^2 = 40 n + 1
    obtain ⟨z, hz⟩ := sqrt_exists (p := 2) (40 * (n : ℤ_[2]) + 1) (by
      have h2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
        have := PadicInt.norm_p (p := 2); push_cast at this; rw [this]; norm_num
      have h8 : ‖(8 : ℤ_[2])‖ = 1 / 8 := by
        have := PadicInt.norm_p_pow (p := 2) 3; push_cast at this; norm_num at this ⊢ <;> linarith
      have : ‖40 * (n : ℤ_[2]) + 1 - 1‖ ≤ 1 / 8 := by
        rw [add_sub_cancel_right, show (40 : ℤ_[2]) * n = 8 * (5 * n) by ring, ← h8]
        exact norm_mul_le_of _ _
      rw [h2]; linarith)
    refine ⟨1, 1, z, ?_, Or.inl isUnit_one⟩
    rw [hz]; ring
  · -- p = 3 : a = 0, b = 2 z, c = 1, z^2 = 6 n + 1
    obtain ⟨z, hz⟩ := sqrt_exists (p := 3) (6 * (n : ℤ_[3]) + 1) (by
      have h2 : ‖(2 : ℤ_[3])‖ = 1 := by
        have := PadicInt.norm_natCast_eq_one_iff (p := 3) (n := 2)
        exact_mod_cast this.mpr (by norm_num)
      have h3 : ‖(3 : ℤ_[3])‖ = 1 / 3 := by
        have := PadicInt.norm_p (p := 3); push_cast at this; rw [this]; norm_num
      have : ‖6 * (n : ℤ_[3]) + 1 - 1‖ ≤ 1 / 3 := by
        rw [add_sub_cancel_right, show (6 : ℤ_[3]) * n = 3 * (2 * n) by ring, ← h3]
        exact norm_mul_le_of _ _
      rw [h2]; linarith)
    refine ⟨0, 2 * z, 1, ?_, Or.inr (Or.inr isUnit_one)⟩
    rw [mul_pow, hz]; ring
  · -- p = 5 : a = b = 1, c^2 = 40 n + 1
    obtain ⟨z, hz⟩ := sqrt_exists (p := 5) (40 * (n : ℤ_[5]) + 1) (by
      have h2 : ‖(2 : ℤ_[5])‖ = 1 := by
        have := PadicInt.norm_natCast_eq_one_iff (p := 5) (n := 2)
        exact_mod_cast this.mpr (by norm_num)
      have h5 : ‖(5 : ℤ_[5])‖ = 1 / 5 := by
        have := PadicInt.norm_p (p := 5); push_cast at this; rw [this]; norm_num
      have : ‖40 * (n : ℤ_[5]) + 1 - 1‖ ≤ 1 / 5 := by
        rw [add_sub_cancel_right, show (40 : ℤ_[5]) * n = 5 * (8 * n) by ring, ← h5]
        exact norm_mul_le_of _ _
      rw [h2]; linarith)
    refine ⟨1, 1, z, ?_, Or.inl isUnit_one⟩
    rw [hz]; ring

end OMA.A287

theorem OMA.solution : OMA.R_OeisA287616_conjecture_R1_H1_R1_H1_R1.H1 := OMA.A287.h1
