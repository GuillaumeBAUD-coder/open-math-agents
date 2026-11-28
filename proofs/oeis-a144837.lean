import OMAStatements.S_oeis_a144837
import Mathlib

namespace OMA.P144837

open OMA.S_oeis_a144837

/-- Binet's formula for the Lucas numbers. -/
lemma lucas_real (m : ℕ) : (lucas m : ℝ) = Real.goldenRatio ^ m + Real.goldenConj ^ m := by
  induction m using Nat.twoStepInduction with
  | zero =>
    simp [lucas]
    norm_num
  | one =>
    simp [lucas, Real.goldenRatio_add_goldenConj]
  | more m ih1 ih2 =>
    have e : lucas (m + 2) = lucas (m + 1) + lucas m := rfl
    rw [e]
    push_cast
    rw [ih1, ih2]
    have h1 := Real.goldenRatio_sq
    have h2 := Real.goldenConj_sq
    linear_combination (-(Real.goldenRatio ^ m)) * h1 + (-(Real.goldenConj ^ m)) * h2

/-- L(5m) = L(m)^5 + 5 L(m)^3 + 5 L(m) for odd m. -/
lemma lucas_five_mul (m : ℕ) (hm : Odd m) :
    lucas (5 * m) = lucas m ^ 5 + 5 * lucas m ^ 3 + 5 * lucas m := by
  have h : ((lucas (5 * m) : ℤ) : ℝ)
      = ((lucas m ^ 5 + 5 * lucas m ^ 3 + 5 * lucas m : ℤ) : ℝ) := by
    push_cast
    rw [lucas_real, lucas_real]
    have hxy : Real.goldenRatio ^ m * Real.goldenConj ^ m = -1 := by
      rw [← mul_pow, Real.goldenRatio_mul_goldenConj]
      exact hm.neg_one_pow
    rw [pow_mul' Real.goldenRatio 5 m, pow_mul' Real.goldenConj 5 m]
    generalize Real.goldenRatio ^ m = x at *
    generalize Real.goldenConj ^ m = y at *
    linear_combination (-(5 * (x + y) ^ 3 - 5 * (x + y) * (x * y - 1))) * hxy
  exact_mod_cast h

lemma a_succ (n : ℕ) : a (n + 1) = a n ^ 5 + 5 * a n ^ 3 + 5 * a n := by
  unfold a
  rw [pow_succ', lucas_five_mul _ (Odd.pow (by decide))]

/-- 5^(2n+1) divides a(n)^2 + 4. -/
lemma dvd_sq_add_four (n : ℕ) : (5 : ℤ) ^ (2 * n + 1) ∣ a n ^ 2 + 4 := by
  induction n with
  | zero => norm_num [a, lucas]
  | succ n ih =>
    rw [a_succ]
    have e : (a n ^ 5 + 5 * a n ^ 3 + 5 * a n) ^ 2 + 4
        = (a n ^ 2 + 4) * (a n ^ 4 + 3 * a n ^ 2 + 1) ^ 2 := by ring
    rw [e]
    have h5 : (5 : ℤ) ∣ a n ^ 4 + 3 * a n ^ 2 + 1 := by
      have h1 : (5 : ℤ) ∣ a n ^ 2 + 4 := Dvd.dvd.trans (dvd_pow_self 5 (by omega)) ih
      obtain ⟨c, hc⟩ := h1
      exact ⟨c * (a n ^ 2 - 1) + 1, by linear_combination (a n ^ 2 - 1) * hc⟩
    have h25 : (5 : ℤ) ^ 2 ∣ (a n ^ 4 + 3 * a n ^ 2 + 1) ^ 2 := pow_dvd_pow_of_dvd h5 2
    have e2 : (5 : ℤ) ^ (2 * (n + 1) + 1) = 5 ^ (2 * n + 1) * 5 ^ 2 := by ring
    rw [e2]
    exact mul_dvd_mul ih h25

end OMA.P144837

theorem OMA.solution : type_of% @OMA.S_oeis_a144837.main := by
  intro n r hn hr
  rw [Int.modEq_iff_dvd]
  have h1 := OMA.P144837.dvd_sq_add_four n
  have h2 : (5 : ℤ) ^ (n + r + 1) ∣ 5 ^ (2 * n + 1) := pow_dvd_pow 5 (by omega)
  have e : OMA.S_oeis_a144837.a n - OMA.S_oeis_a144837.a (n + 1)
      = (OMA.S_oeis_a144837.a n ^ 2 + 4)
        * (-(OMA.S_oeis_a144837.a n * (OMA.S_oeis_a144837.a n ^ 2 + 1))) := by
    rw [OMA.P144837.a_succ]
    ring
  rw [e]
  exact Dvd.dvd.mul_right (h2.trans h1) _
